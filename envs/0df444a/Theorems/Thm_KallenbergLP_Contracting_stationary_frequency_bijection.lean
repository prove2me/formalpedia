-- Prove2me | Theorems.Thm_KallenbergLP_Contracting_stationary_frequency_bijection
-- name    : KallenbergLP.Contracting.stationary_frequency_bijection
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:35:50.135367+00:00
-- url     : https://prove2.me/theorems/27e006c8-afe7-4630-b7f2-378b15de5428
-- title:
--   Theorem 3.4.2 — stationary policies and feasible LP frequencies
-- statement:
--   Suppose the initial weights satisfy $\beta_i>0$ for every state of a finite contracting model. A stationary randomized rule $\pi$ is mapped to its state-action frequency vector
--
--   $$x_{ia}(\pi)=[\beta^T(I-P(\pi))^{-1}]_i\pi_{ia}.$$
--
--   This map is a bijection onto the feasible solutions of linear program (3.3.7). Its inverse is $\pi_{ia}(x)=x_{ia}/x_i$, where $x_i=\sum_a x_{ia}$. A stationary policy is pure exactly when its frequency vector is an extreme feasible point.
--
--   The correspondence connects policy selection with the geometry of the equality-constrained frequency polytope.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 64, Theorem 3.4.2; p. 53, equations (3.3.7) and (3.3.8); p. 54, equation (3.3.11)

import Mathlib
import Definitions.Def_KallenbergLP_Contracting_Occupation

namespace KallenbergLP.Contracting

/-- Kallenberg (1983), Theorem 3.4.2, p. 64. -/
theorem stationary_frequency_bijection
    {E : Type} [Fintype E] [Nonempty E]
    {A : E → Type} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    (M : FiniteMDP E A) (_C : Contraction M)
    (β : E → ℝ) (hβ : ∀ i, 0 < β i) :
    (∀ q : StationaryRule E A, IsStationaryRule q →
      M.stationaryFrequency β q ∈ M.feasibleFrequency β) ∧
    (∀ x : StationaryRule E A, x ∈ M.feasibleFrequency β →
      IsStationaryRule (FiniteMDP.ruleOfFrequency x) ∧
      M.stationaryFrequency β (FiniteMDP.ruleOfFrequency x) = x) ∧
    (∀ q : StationaryRule E A, IsStationaryRule q →
      FiniteMDP.ruleOfFrequency (M.stationaryFrequency β q) = q) ∧
    (∀ q : StationaryRule E A, IsStationaryRule q →
      ((∃ f : PureRule E A, q = pureRule f) ↔
        M.stationaryFrequency β q ∈ (M.feasibleFrequency β).extremePoints ℝ)) := by sorry

end KallenbergLP.Contracting
