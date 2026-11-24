-- Prove2me | Theorems.Thm_GallegoOzerADI_PositiveSetup_Supplement_value_horizon_monotone
-- name    : GallegoOzerADI.PositiveSetup.Supplement.value_horizon_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T00:41:25.399389+00:00
-- url     : https://prove2.me/theorems/32d4d78b-8d0a-40e4-8ff9-a4f1d07eb132
-- title:
--   Lemma 4 (corrected: nonnegative single-period cost) — stationary costs increase with the number of remaining periods
-- statement:
--   Consider the stationary inventory problem with advance demand information and positive set-up cost: lead time $L\ge0$, $M\ge1$ observed demands beyond the protection period, single-period cost $G$ convex with $G(y)\to\infty$ as $|y|\to\infty$, set-up cost $K>0$, discount factor $\alpha>0$, and i.i.d. demand vectors whose law $\mu$ is a probability measure with nonnegative components. Let $J_n$ and $V_n$ be the optimal cost and the cost-to-go with $n$ further periods (so the paper's $J_t$, $V_t$ in a horizon-$T$ problem are $J_{T+1-t}$, $V_{T-t}$). Assume moreover $G(y)\ge0$ for all $y$. Then for every $n\ge0$, every inventory position $x\in\mathbb R$ and every observed-demand vector $o\ge0$,
--   $$
--   V_n(x,o)\le V_{n+1}(x,o)\qquad\text{and}\qquad J_n(x,o)\le J_{n+1}(x,o).
--   $$
--   In the paper's notation: $V_{t-1}(x,o)\ge V_t(x,o)$ and $J_{t-1}(x,o)\ge J_t(x,o)$; managing the system for one more period cannot cost less. The lemma is used to pass to the limit $T\to\infty$ in Theorem 3.
--
--   **Formalization Note.** The paper's §2 hypotheses are taken on the primitives exactly as in the published base model, without its linear-growth and moment conditions; $o$ ranges over the reachable nonnegative observation vectors.
--
--   Differences from the source:
--   - correction: no sign condition on the single-period cost G → G(y) ≥ 0 for all y; reason: the proof of Lemma 5 (p. 1358) states that the horizon monotonicity follows from dynamic programming with nonnegative cost and the proof of Lemma 4 uses it at t = T; without it the lemma is false: G(y) = |y| − 10 gives J_1(0,o) ≤ G(0) = −10 < 0 = J_0(0,o) (DISPROOF.md)
--   - reading: for all t, V_{t−1}, V_t, J_{t−1}, J_t of a horizon-T problem → for all n ≥ 0, V_{n+1}, V_n, J_{n+1}, J_n with n further periods; reason: stationary values depend only on the time to go T − t (p. 1351)
--   - reading: any fixed vector (x, o) → every real x and every o ≥ 0; reason: observed demands are cumulative customer orders, nonnegative on every reachable state (§2)
--   - reading: discount factor α of unstated sign → 0 < α; reason: discount factors are positive throughout the paper; the paper never states it
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1351, Lemma 4; proof p. 1358

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_SetupCost
import Definitions.Def_GallegoOzerADI_PositiveSetup_Model
import Definitions.Def_GallegoOzerADI_PositiveSetup_Supplement_ControlSystem
import Definitions.Def_GallegoOzerADI_PositiveSetup_Supplement_Stationary

open MeasureTheory Filter Topology

namespace GallegoOzerADI.PositiveSetup.Supplement

/-- Lemma 4 (p. 1351): in the stationary positive set-up cost problem, one more remaining period
never lowers the cost: `V_{t-1}(x, o) ≥ V_t(x, o)` and `J_{t-1}(x, o) ≥ J_t(x, o)`. -/
theorem value_horizon_monotone {L M : ℕ} [NeZero M] (G : ℝ → ℝ) (K α : ℝ)
    (μ : Measure (Fin (L + M + 2) → ℝ)) [IsProbabilityMeasure μ]
    (hG_convex : ConvexOn ℝ Set.univ G) (hG_coercive : Tendsto G (cocompact ℝ) atTop)
    (hG_nonneg : ∀ y, 0 ≤ G y) (hK : 0 < K) (hα : 0 < α)
    (hμ_nonneg : ∀ᵐ D ∂μ, ∀ k, 0 ≤ D k) :
    ∀ (n : ℕ) (x : ℝ) (o : Fin M → ℝ), 0 ≤ o →
      Vgo G K α μ n x o ≤ Vgo G K α μ (n + 1) x o ∧
        Jgo G K α μ n x o ≤ Jgo G K α μ (n + 1) x o := by sorry

end GallegoOzerADI.PositiveSetup.Supplement
