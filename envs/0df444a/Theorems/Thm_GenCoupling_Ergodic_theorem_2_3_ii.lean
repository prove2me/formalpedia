-- Prove2me | Theorems.Thm_GenCoupling_Ergodic_theorem_2_3_ii
-- name    : GenCoupling.Ergodic.theorem_2_3_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:47.405526+00:00
-- url     : https://prove2.me/theorems/1060fd87-306d-4815-b5e9-a47424b9ee8e
-- title:
--   Theorem 2.3(ii), p. 8 — under B1 for t₀ and B, the set B is d_N-small for P_{t₀} for every N > 0
-- statement:
--   Let $(E,\rho)$ be a Polish space, $\{P_t\}$ a Markov semigroup on $E$ and $\theta$ a premetric. Assume that Assumption B1 holds for some $t_0>0$ and a set $B\subset E$: for every $\varepsilon>0$ there is a measurable $D$ with $\inf_{x\in B}P_{t_0}(x,D)>0$ and $\sup_{x,y\in D}\theta(x,y)\le\varepsilon$.
--
--   Then for every $N>0$ the set $B$ is $d_N$-small for $P_{t_0}$: for some $\varepsilon>0$,
--   $$\sup_{x,y\in B}W_{d_N}(P_{t_0}(x,\cdot),P_{t_0}(y,\cdot))\le 1-\varepsilon.$$
--
--   Theorem 2.5 applies this to the level sets $B=\{V\le M\}$ of the Lyapunov function to obtain condition 4 of Proposition 2.1.
-- source:
--   Butkovsky, Kulik and Scheutzow, Generalized couplings and ergodic rates for SPDEs and other Markov models, arXiv:1806.00395v3, p. 8, Theorem 2.3(ii)

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_GenCoupling_Ergodic_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GenCoupling.Ergodic

/-- Theorem 2.3(ii), p. 8: if B1 holds for `t₀ > 0` and `B`, then for every `N > 0` the set `B`
is `d_N`-small for `P_{t₀}`. -/
theorem theorem_2_3_ii {E : Type*} [MetricSpace E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (P : ℝ≥0 → Kernel E E) (hP : IsMarkovSemigroup P)
    (θ : E → E → ℝ) (hθ : IsPremetric θ) (B : Set E) (t₀ : ℝ≥0)
    (hB1 : AssumptionB1 θ P B t₀) (N : ℝ) (hN : 0 < N) :
    IsSmall P t₀ (dN θ N) B := by sorry

end GenCoupling.Ergodic
