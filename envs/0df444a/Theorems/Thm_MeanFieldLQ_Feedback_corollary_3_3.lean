-- Prove2me | Theorems.Thm_MeanFieldLQ_Feedback_corollary_3_3
-- name    : MeanFieldLQ.Feedback.corollary_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:36:06.878903+00:00
-- url     : https://prove2.me/theorems/b5ba917c-c778-40e6-9703-b506fb637968
-- title:
--   Corollary 3.3, p. 2822 — the MF-FBSDE (3.3) is uniquely solvable and yields the unique optimal pair
-- statement:
--   Assume (H1)–(H2) and let $x\in\mathbb R^n$.
--
--   1. The MF-FBSDE (3.3) with initial state $x$ has an adapted solution $(X^*,u^*,Y,Z)$.
--   2. It is unique: for any two adapted solutions, $X^*(t)$ and $Y(t)$ agree almost surely for every $t\in[0,T]$, and $u^*$ and $Z$ agree $ds\otimes d\mathbb P$-a.e. on $[0,T]\times\Omega$.
--   3. For every adapted solution, $(X^*,u^*)$ is an optimal pair of Problem (MF-LQ). It is the unique one: every optimal pair $(X',u')$ for $x$ has $u'=u^*$ $ds\otimes d\mathbb P$-a.e. and $X'(t)=X^*(t)$ a.s. for every $t\in[0,T]$.
--
--   Section 4 of the paper decouples this forward–backward system by Riccati equations.
-- source:
--   Yong, Linear-Quadratic Optimal Control Problems for Mean-Field Stochastic Differential Equations, SIAM J. Control Optim. 51(4) (2013), p. 2822, Corollary 3.3

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_MeanFieldLQ_Feedback_Setting

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal ENNReal

namespace MeanFieldLQ.Feedback

/-- Corollary 3.3 (p. 2822): under (H1)–(H2), for every `x` the MF-FBSDE (3.3) has an adapted
solution `(X*, u*, Y, Z)`; it is unique (`X*`, `Y` at every `t ∈ [0, T]` a.s.; `u*`, `Z`
`ds ⊗ dP`-a.e.); and for every adapted solution, `(X*, u*)` is an optimal pair and every optimal pair
has the same control (`ds ⊗ dP`-a.e.) and the same state (at every `t ∈ [0, T]` a.s.). -/
theorem corollary_3_3 {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [μ.IsComplete] {W : ℝ≥0 → Ω → Fin 1 → ℝ} (hW : Peng1990.SMP.IsStdBrownian μ W)
    (T : ℝ≥0) (hT : 0 < T) (d : Data n m)
    (δ : ℝ) (h1 : H1 T d) (h2 : H2 T δ d) (x : Fin n → ℝ) :
    (∃ (X : ℝ≥0 → Ω → Fin n → ℝ) (u : ℝ≥0 → Ω → Fin m → ℝ) (Y Z : ℝ≥0 → Ω → Fin n → ℝ),
        IsFBSDESol μ hW T d x X u Y Z) ∧
      (∀ (X X' : ℝ≥0 → Ω → Fin n → ℝ) (u u' : ℝ≥0 → Ω → Fin m → ℝ)
          (Y Y' Z Z' : ℝ≥0 → Ω → Fin n → ℝ),
          IsFBSDESol μ hW T d x X u Y Z → IsFBSDESol μ hW T d x X' u' Y' Z' →
            (∀ t ≤ T, X t =ᵐ[μ] X' t) ∧ AEEqOn μ T u u' ∧
              (∀ t ≤ T, Y t =ᵐ[μ] Y' t) ∧ AEEqOn μ T Z Z') ∧
      ∀ (X : ℝ≥0 → Ω → Fin n → ℝ) (u : ℝ≥0 → Ω → Fin m → ℝ) (Y Z : ℝ≥0 → Ω → Fin n → ℝ),
        IsFBSDESol μ hW T d x X u Y Z →
          IsOptimalPair μ hW T d x u X ∧
            ∀ (u' : ℝ≥0 → Ω → Fin m → ℝ) (X' : ℝ≥0 → Ω → Fin n → ℝ),
              IsOptimalPair μ hW T d x u' X' → AEEqOn μ T u u' ∧ ∀ t ≤ T, X t =ᵐ[μ] X' t := by sorry

end MeanFieldLQ.Feedback
