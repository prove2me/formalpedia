-- Prove2me | Theorems.Thm_GallegoOzerADI_PositiveSetup_Supplement_zero_setup_horizon_monotone
-- name    : GallegoOzerADI.PositiveSetup.Supplement.zero_setup_horizon_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:42:40.286841+00:00
-- url     : https://prove2.me/theorems/d935a561-42cd-4d0e-8157-ca86d8481e65
-- title:
--   Lemma 5 (corrected: nonnegative single-period cost) — zero set-up cost: values, slopes and base-stock levels across horizons
-- statement:
--   Consider the stationary inventory problem with advance demand information and zero set-up cost ($K=0$): lead time $L\ge0$, $M\ge1$ observed demands beyond the protection period, single-period cost $G$ convex with $G(y)\to\infty$ as $|y|\to\infty$, discount factor $\alpha>0$, and i.i.d. demand vectors whose law $\mu$ is a probability measure with nonnegative components. Let $J_n$, $V_n$ be the optimal cost and the cost-to-go with $n$ further periods (the paper's $J_t$, $V_t$ of a horizon-$T$ problem are $J_{T+1-t}$, $V_{T-t}$), let $y_n(o)$ be the smallest minimizer of $V_n(\cdot,o)$, and let $\nabla F(x,o)=F(x+1,o)-F(x,o)$. Then for every $n\ge0$, every $x\in\mathbb R$ and every $o\ge0$:
--
--   1. if $G(y)\ge0$ for all $y$, then $V_n(x,o)\le V_{n+1}(x,o)$;
--   2. if $G(y)\ge0$ for all $y$, then $J_n(x,o)\le J_{n+1}(x,o)$;
--   3. $\nabla V_n(x,o)\le\nabla V_{n+1}(x,o)$;
--   4. $y_{n+1}(o)\le y_n(o)$;
--   5. $\nabla J_n(x,o)\le\nabla J_{n+1}(x,o)$.
--
--   In the paper's notation: $V_{t-1}\ge V_t$, $J_{t-1}\ge J_t$, $\nabla V_{t-1}\ge\nabla V_t$, $y_{t-1}(o)\le y_t(o)$ and $\nabla J_{t-1}\ge\nabla J_t$. The appendix uses the lemma for the limits in Theorem 6 and for the stationary case of Theorem 5.
--
--   **Formalization Note.** The inventory variable is real and the forward differences are taken at every real $x$. The §2 hypotheses are taken on the primitives without growth or moment conditions.
--
--   Differences from the source:
--   - correction: no sign condition on the single-period cost G → G(y) ≥ 0 for all y, as a premise of parts 1–2 only (parts 3–5 carry no sign condition); reason: the proof on p. 1358 derives the monotonicity of V_t and J_t from dynamic programming with nonnegative cost; without it parts 1–2 are false: G(y) = |y| − 10 gives J_1(0,o) = −10 < 0 = J_0(0,o) (DISPROOF.md)
--   - reading: for all t, the paper's V_{t−1}, V_t, J_{t−1}, J_t, y_{t−1}, y_t of a horizon-T problem → for all n ≥ 0, the quantities with n + 1 and n further periods; reason: stationary values depend only on the time to go T − t (p. 1352)
--   - reading: unspecified (x, o) → every real x and every o ≥ 0; reason: observed demands are nonnegative on every reachable state (§2)
--   - reading: discount factor α of unstated sign → 0 < α; reason: discount factors are positive throughout the paper; the paper never states it
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1351, Lemma 5; proof pp. 1358–1359; ∇ defined on p. 1356

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_SetupCost
import Definitions.Def_GallegoOzerADI_PositiveSetup_Model
import Definitions.Def_GallegoOzerADI_PositiveSetup_Supplement_ControlSystem
import Definitions.Def_GallegoOzerADI_PositiveSetup_Supplement_Stationary
import Definitions.Def_GallegoOzerADI_PositiveSetup_Supplement_ForwardDifference

open MeasureTheory Filter Topology

namespace GallegoOzerADI.PositiveSetup.Supplement

/-- Lemma 5 (p. 1351): in the stationary zero set-up cost problem (`K = 0`), with one more
remaining period: `V_{t-1} ≥ V_t`, `J_{t-1} ≥ J_t`, `∇V_{t-1} ≥ ∇V_t`, `y_{t-1}(o) ≤ y_t(o)`
and `∇J_{t-1} ≥ ∇J_t`, where `∇F(x, o) = F(x + 1, o) − F(x, o)`. The first two inequalities
carry the nonnegative single-period cost premise that the paper's proof invokes; the last three
need no sign condition on `G`. -/
theorem zero_setup_horizon_monotone {L M : ℕ} [NeZero M] (G : ℝ → ℝ) (α : ℝ)
    (μ : Measure (Fin (L + M + 2) → ℝ)) [IsProbabilityMeasure μ]
    (hG_convex : ConvexOn ℝ Set.univ G) (hG_coercive : Tendsto G (cocompact ℝ) atTop)
    (hα : 0 < α) (hμ_nonneg : ∀ᵐ D ∂μ, ∀ k, 0 ≤ D k) :
    ∀ (n : ℕ) (x : ℝ) (o : Fin M → ℝ), 0 ≤ o →
      ((∀ y, 0 ≤ G y) →
        Vgo G 0 α μ n x o ≤ Vgo G 0 α μ (n + 1) x o ∧
          Jgo G 0 α μ n x o ≤ Jgo G 0 α μ (n + 1) x o) ∧
        fwdDiff (Vgo G 0 α μ n) x o ≤ fwdDiff (Vgo G 0 α μ (n + 1)) x o ∧
        orderUpToLevel G 0 α μ (n + 1) o ≤ orderUpToLevel G 0 α μ n o ∧
        fwdDiff (Jgo G 0 α μ n) x o ≤ fwdDiff (Jgo G 0 α μ (n + 1)) x o := by sorry

end GallegoOzerADI.PositiveSetup.Supplement
