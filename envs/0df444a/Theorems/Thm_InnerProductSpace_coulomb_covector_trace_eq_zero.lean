-- Prove2me | Theorems.Thm_InnerProductSpace_coulomb_covector_trace_eq_zero
-- name    : InnerProductSpace.coulomb_covector_trace_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T21:57:27.289106+00:00
-- url     : https://prove2.me/theorems/63344236-dcc7-4249-a736-8f195182eba2
-- title:
--   The Coulomb radial covector field has zero divergence off the origin
-- statement:
--   Let $n\ge2$ and $c\in\mathbb R$. On punctured Euclidean space define the covector field
--
--   $$Q(z)[w]=\frac{c}{|z|^n}\langle z,w\rangle.$$
--
--   For every $z\ne0$ and every orthonormal basis $(e_i)$,
--
--   $$\sum_i DQ(z)[e_i](e_i)=0.$$
--
--   This is the local Coulomb-field divergence calculation. It supplies harmonicity away from the singularity for kernels with gradient $c z/|z|^n$, including the logarithmic kernel in dimension two.
-- source:
--   Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, printed p. 33, Section 2.6.1 and Eq. (2.14): harmonicity off zero and radial gradient of the fundamental solution; generalized to arbitrary real gradient coefficient.

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination

open MeasureTheory Set

theorem InnerProductSpace.coulomb_covector_trace_eq_zero (n : ℕ) (hn : 2 ≤ n) (c : ℝ)
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ≠ 0) :
    (∑ i : Fin n,
      fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) =>
        (c / ‖y‖ ^ n) • innerSL ℝ y) z
          (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ i)) = 0 := by sorry
