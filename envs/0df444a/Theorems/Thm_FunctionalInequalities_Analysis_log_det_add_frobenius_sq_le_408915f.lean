-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_log_det_add_frobenius_sq_le_408915f
-- name    : FunctionalInequalities.Analysis.log_det_add_frobenius_sq_le_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:11:41.439053+00:00
-- url     : https://prove2.me/theorems/fec2ec8b-5bed-4741-9373-ea3f81f2e4ac
-- title:
--   Quantitative Concavity of Log Determinant
-- statement:
--   This is the quantitative matrix log-determinant inequality cited in the module documentation in connection with Lemma 4.2 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $A,B$ be real $n\times n$ matrices and $K\in\mathbb R$. Assume:
--
--   1. $A$ and $B$ are positive definite.
--   2. $K I-A$ is positive semidefinite.
--   3. $K I-B$ is positive semidefinite.
--
--   Then
--
--   $$\log\det B+\frac{\|B-A\|_F^2}{2K^2}
--   \le \log\det A+\operatorname{tr}\!\left(A^{-1}(B-A)\right),$$
--
--   where $\|B-A\|_F^2=\sum_{i,j}(B_{ij}-A_{ij})^2$. The declaration `log_det_add_frobenius_sq_le` is a finite-dimensional matrix inequality; positivity and the upper bounds are expressed through `PosDef` and `PosSemidef`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/LogDet.lean#L344-L484 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.LogDet`, declaration `FunctionalInequalities.Analysis.log_det_add_frobenius_sq_le`; the repository is private at upload time).

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Trace

noncomputable section
open Matrix
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section LogDetConcavity
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.log_det_add_frobenius_sq_le_408915f {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ} {K : ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hAK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef)
    (hBK : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - B).PosSemidef) :
    Real.log B.det + (∑ i, ∑ j, (B - A) i j ^ 2) / (2 * K ^ 2) ≤
      Real.log A.det + (A⁻¹ * (B - A)).trace := by sorry
