-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_fderiv_det_eq_det_mul_trace_408915f
-- name    : FunctionalInequalities.Analysis.fderiv_det_eq_det_mul_trace_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:22:21.92699+00:00
-- url     : https://prove2.me/theorems/b6089ab5-d130-4a3b-8fe1-11c90fe299b1
-- title:
--   Jacobi Formula for the Determinant
-- statement:
--   This is Jacobi’s formula for a real square matrix.
--
--   Let $M,N$ be matrices indexed by a finite type, and assume $\det M$ is a unit, equivalently that $M$ is invertible. Then the Fréchet derivative of the determinant at $M$ in direction $N$ is
--
--   $$
--   D(\det)_M[N]=\det(M)\,\operatorname{tr}(M^{-1}N).
--   $$
--
--   The result is a finite-dimensional algebraic identity and imposes no symmetry, positivity, or regularity assumptions on $M$ or $N$. In Lean it is expressed by `fderiv ℝ Matrix.det M N` and matrix multiplication and trace.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/DeterminantDerivative.lean#L45-L68 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.DeterminantDerivative`, declaration `FunctionalInequalities.Analysis.fderiv_det_eq_det_mul_trace`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_DeterminantDerivative
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Algebra.Group.Matrix

noncomputable section
open scoped Matrix.Norms.Elementwise
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem FunctionalInequalities.Analysis.fderiv_det_eq_det_mul_trace_408915f (M N : Matrix ι ι ℝ) (hM : IsUnit M.det) :
    fderiv ℝ Matrix.det M N = M.det * Matrix.trace (M⁻¹ * N) := by sorry
