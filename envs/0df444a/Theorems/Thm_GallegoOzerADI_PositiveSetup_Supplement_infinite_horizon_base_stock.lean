-- Prove2me | Theorems.Thm_GallegoOzerADI_PositiveSetup_Supplement_infinite_horizon_base_stock
-- name    : GallegoOzerADI.PositiveSetup.Supplement.infinite_horizon_base_stock
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T00:43:14.409246+00:00
-- url     : https://prove2.me/theorems/bd8c7945-c194-4268-a856-dc76a47b99ad
-- title:
--   Theorem 6 (corrected: uniform convergence on every half-line $(-\infty,B]$) — zero set-up cost: the myopic base-stock level is infinite-horizon optimal
-- statement:
--   Consider the stationary inventory problem with advance demand information and zero set-up cost ($K=0$): lead time $L\ge0$, $M\ge1$ observed demands beyond the protection period, single-period cost $G$ convex with $G(y)\to\infty$ as $|y|\to\infty$, discount factor $0<\alpha<1$, and i.i.d. demand vectors whose law $\mu$ is a probability measure with nonnegative components. Let $J_n$, $V_n$ be the optimal cost and the cost-to-go with $n$ further periods ($T\to\infty$ with $t$ fixed is $n\to\infty$) and let
--   $$
--   y^m=\min\{y:G(y)=\min_xG(x)\}.
--   $$
--   Then there are functions $J(x,o)$ and $V(x,o)$ such that for every observed-demand vector $o\ge0$:
--
--   1. for every $B\in\mathbb R$, $J_n(\cdot,o)\to J(\cdot,o)$ uniformly on $(-\infty,B]$; $J(\cdot,o)$ is convex; and $J(x,o)\to\infty$ as $x\to\infty$;
--   2. for every $B\in\mathbb R$, $V_n(\cdot,o)\to V(\cdot,o)$ uniformly on $(-\infty,B]$; $V(\cdot,o)$ is convex; $V(x,o)\to\infty$ as $|x|\to\infty$; and $V(\cdot,o)$ has a finite minimizer;
--   3. $y^m$ is the smallest minimizer $y(o)$ of $V(\cdot,o)$, and the base-stock policy that orders up to $\max(x,y^m)$ is admissible and optimal for the infinite-horizon problem from every state $(x,o)$.
--
--   The infinite-horizon problem minimizes $\mathbb E\sum_{k\ge0}\alpha^k G(y_k)$ over all admissible policies, including history-dependent ones. The theorem says that, in the stationary zero set-up cost case, observed demand beyond the protection period does not change the optimal order-up-to level even over an infinite horizon.
--
--   **Formalization Note.** No sign, growth or moment condition is placed on $G$. The expected discounted cost is $\mathbb E[\sum(\alpha^kc_k)^+]-\mathbb E[\sum(\alpha^kc_k)^-]$ in the extended reals.
--
--   Differences from the source:
--   - correction: J_t(·,o) and V_t(·,o) converge uniformly (on the whole inventory line) → uniformly on every half-line (−∞, B]; reason: the printed claim is false: with L = 0, N = 2, deterministic D = (1,0,0), o = 0, G(y) = |y − 1|, α = 1/2, J − J_n ≥ α^n(x − n − 1) for x ≥ n + 1 and V − V_n ≥ α^{n+1}(y − n − 2) for y ≥ n + 2, so both suprema are infinite for every n (DISPROOF.md); the proof on p. 1358 only gives an initial-state-dependent bound
--   - reading: the infinite-horizon problem with an unstated discount range → 0 < α < 1; reason: the proof on p. 1358 divides by 1 − α; the infinite-horizon problems are discounted
--   - reading: an optimal policy for the infinite-horizon problem → the infimum, over admissible measurable non-anticipative deterministic history-dependent policies, of E[Σ(α^k c_k)^+] − E[Σ(α^k c_k)^−] with c_k = G(y_k) and i.i.d. demand vectors, attained by the base-stock policy max(x, y^m); reason: Eq. (12) of Appendix A with T = ∞ and K = 0; randomized policies are not in the class
--   - reading: y(o) = y^m with y(o) a finite minimizer of V(·,o) → y^m is the smallest minimizer of V(·,o); reason: the paragraph before Theorem 6 (p. 1352) identifies the base-stock level with the smallest minimizer
--   - reading: for any fixed vector o, with the paper's J_t, V_t of a horizon-T problem → for every o ≥ 0, with J_n, V_n of n further periods and n → ∞; reason: stationary values depend only on T − t (p. 1352); observed demands are nonnegative on reachable states
-- source:
--   Gallego, Özer, Integrating Replenishment Decisions with Advance Demand Information, Management Science 47(10):1344–1360 (2001), p. 1352, Theorem 6; proof p. 1358

import Mathlib
import Definitions.Def_GallegoOzerADI_PositiveSetup_SetupCost
import Definitions.Def_GallegoOzerADI_PositiveSetup_Model
import Definitions.Def_GallegoOzerADI_PositiveSetup_Supplement_ControlSystem
import Definitions.Def_GallegoOzerADI_PositiveSetup_Supplement_Stationary
import Definitions.Def_GallegoOzerADI_PositiveSetup_MyopicLevels

open MeasureTheory Filter Topology

namespace GallegoOzerADI.PositiveSetup.Supplement

/-- Theorem 6 (p. 1352), stationary zero set-up cost (`K = 0`), infinite horizon, with the
global uniform convergence of Parts 1–2 corrected to uniform convergence on every half-line
`(-∞, B]` (see the item's Differences from the source). `myopicOrderUpTo G` is
`y^m = min {y : G(y) = min_x G(x)}`. -/
theorem infinite_horizon_base_stock {L M : ℕ} [NeZero M] (G : ℝ → ℝ) (α : ℝ)
    (μ : Measure (Fin (L + M + 2) → ℝ)) [IsProbabilityMeasure μ]
    (hG_convex : ConvexOn ℝ Set.univ G) (hG_coercive : Tendsto G (cocompact ℝ) atTop)
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (hμ_nonneg : ∀ᵐ D ∂μ, ∀ k, 0 ≤ D k) :
    ∃ J V : ℝ → (Fin M → ℝ) → ℝ, ∀ o : Fin M → ℝ, 0 ≤ o →
      -- Part 1
      ((∀ B : ℝ, TendstoUniformlyOn (fun n x => Jgo G 0 α μ n x o) (fun x => J x o) atTop
          (Set.Iic B)) ∧
        ConvexOn ℝ Set.univ (fun x => J x o) ∧ Tendsto (fun x => J x o) atTop atTop) ∧
      -- Part 2
      ((∀ B : ℝ, TendstoUniformlyOn (fun n y => Vgo G 0 α μ n y o) (fun y => V y o) atTop
          (Set.Iic B)) ∧
        ConvexOn ℝ Set.univ (fun y => V y o) ∧ Tendsto (fun y => V y o) (cocompact ℝ) atTop ∧
        ∃ y, ∀ z, V y o ≤ V z o) ∧
      -- Part 3
      (IsLeast {y | ∀ z, V y o ≤ V z o} (myopicOrderUpTo G) ∧
        ∀ x : ℝ, (adiSystem (L := L) G 0).IsOptimalFrom α μ
          (baseStockPolicy (myopicOrderUpTo G)) (x, o)) := by sorry

end GallegoOzerADI.PositiveSetup.Supplement
