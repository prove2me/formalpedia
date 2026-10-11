-- Prove2me | Theorems.Thm_HunterPDE_Newtonian_norm_fderiv_secondPartial_le
-- name    : HunterPDE.Newtonian.norm_fderiv_secondPartial_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T17:50:49.070299+00:00
-- url     : https://prove2.me/theorems/dc3824c8-46af-4c26-80dc-44447def365e
-- title:
--   Uniform derivative bound for the Newtonian Hessian
-- statement:
--   Let $n\ge2$ and let $\Gamma$ be the Newtonian fundamental solution. There is $C_n\ge0$, uniform over all coordinate indices $i,j$, such that the Hessian kernel $K_{ij}=\partial_{ij}\Gamma$ is differentiable at every $z\ne0$ and
--
--   $$\|DK_{ij}(z)\|\le C_n |z|^{-n-1}.$$
--
--   The norm is the operator norm of the Frechet derivative. This is the smoothness estimate used in the far part of a singular-integral Holder bound.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf, printed pp. 41-42, Theorem 2.28 proof, part (b1); explicit derivative bound underlying the asserted homogeneity of DK.

import Theorems.Thm_HunterPDE_Newtonian_secondPartial_formula
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open HunterPDE.Newtonian Filter
open scoped Topology

theorem HunterPDE.Newtonian.norm_fderiv_secondPartial_le (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i j : Fin n,
      ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 →
      DifferentiableAt ℝ (secondPartial (fundamentalSolution n) i j) z ∧
      ‖fderiv ℝ (secondPartial (fundamentalSolution n) i j) z‖ ≤
        C * ‖z‖ ^ (-(n : ℝ) - 1) := by sorry
