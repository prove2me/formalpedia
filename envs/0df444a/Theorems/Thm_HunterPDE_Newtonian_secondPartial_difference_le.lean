-- Prove2me | Theorems.Thm_HunterPDE_Newtonian_secondPartial_difference_le
-- name    : HunterPDE.Newtonian.secondPartial_difference_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T17:58:20.848902+00:00
-- url     : https://prove2.me/theorems/2e9d28a8-9f55-4fca-b8f4-54c5b8a16cc1
-- title:
--   Far-field difference bound for the Newtonian Hessian
-- statement:
--   Let $n\ge2$ and $K_{ij}=\partial_{ij}\Gamma$. There is $C_n\ge0$, uniform over coordinate indices, such that for $z\ne0$ and $|h|\le |z|/2$,
--
--   $$|K_{ij}(z+h)-K_{ij}(z-h)|\le C_n |h| |z|^{-n-1}.$$
--
--   This symmetric formulation applies to two source centres by taking $z$ as the midpoint displacement and $h$ as half their separation. The case $h=0$ is included.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf, printed pp. 41-42, Theorem 2.28 proof, part (b1); symmetric midpoint formulation of the mean-value kernel difference estimate.

import Theorems.Thm_HunterPDE_Newtonian_norm_fderiv_secondPartial_le
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

open HunterPDE.Newtonian

theorem HunterPDE.Newtonian.secondPartial_difference_le (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i j : Fin n,
      ∀ z h : EuclideanSpace ℝ (Fin n), z ≠ 0 → ‖h‖ ≤ ‖z‖ / 2 →
      |secondPartial (fundamentalSolution n) i j (z + h) -
        secondPartial (fundamentalSolution n) i j (z - h)| ≤
        C * ‖h‖ * ‖z‖ ^ (-(n : ℝ) - 1) := by sorry
