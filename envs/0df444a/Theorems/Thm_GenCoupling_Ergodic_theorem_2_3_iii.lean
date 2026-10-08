-- Prove2me | Theorems.Thm_GenCoupling_Ergodic_theorem_2_3_iii
-- name    : GenCoupling.Ergodic.theorem_2_3_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:46.932987+00:00
-- url     : https://prove2.me/theorems/90a7ab88-b78c-416a-a3cd-b367f4aefb0f
-- title:
--   Theorem 2.3(iii), p. 8 — under B2 for R, B, ε, the set B is d_N-small for P_t whenever N R(t) ≤ ε/2
-- statement:
--   Let $(E,\rho)$ be a Polish space, $\{P_t\}$ a Markov semigroup and $\theta$ a premetric. Assume that Assumption B2 holds for a function $R$, a set $B\subset E$ and $\varepsilon>0$: for all $x,y\in B$ there is a generalized coupling with $\mathrm{Law}(X^{x,y}_t)=P_t(x,\cdot)$, $d_{TV}(\mathrm{Law}(Y^{x,y}_t),P_t(y,\cdot))\le1-\varepsilon$ and $\mathsf E\theta(X^{x,y}_t,Y^{x,y}_t)\le R(t)$.
--
--   Then for any $N>0$, $t>0$ such that
--   $$N R(t)\le\varepsilon/2$$
--   the set $B$ is $d_N$-small for $P_t$.
--
--   Theorem 2.6 uses this, with $B=\{V\le4K/\gamma\}$, in place of Theorem 2.3(ii).
-- source:
--   Butkovsky, Kulik and Scheutzow, Generalized couplings and ergodic rates for SPDEs and other Markov models, arXiv:1806.00395v3, p. 8, Theorem 2.3(iii)

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_GenCoupling_Ergodic_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GenCoupling.Ergodic

/-- Theorem 2.3(iii), p. 8: if B2 holds for `R`, `B` and `ε > 0`, then for every `N > 0`,
`t > 0` with `N R(t) ≤ ε/2` the set `B` is `d_N`-small for `P_t`. -/
theorem theorem_2_3_iii {E : Type*} [MetricSpace E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (P : ℝ≥0 → Kernel E E) (hP : IsMarkovSemigroup P)
    (θ : E → E → ℝ) (hθ : IsPremetric θ) (B : Set E) (R : ℝ≥0 → ℝ) (ε : ℝ)
    (hB2 : AssumptionB2 θ P B R ε) (N : ℝ) (t : ℝ≥0) (hN : 0 < N) (ht : 0 < t)
    (hNR : N * R t ≤ ε / 2) :
    IsSmall P t (dN θ N) B := by sorry

end GenCoupling.Ergodic
