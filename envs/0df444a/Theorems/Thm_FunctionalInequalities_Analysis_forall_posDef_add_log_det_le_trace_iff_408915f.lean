-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_forall_posDef_add_log_det_le_trace_iff_408915f
-- name    : FunctionalInequalities.Analysis.forall_posDef_add_log_det_le_trace_iff_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:19:19.748115+00:00
-- url     : https://prove2.me/theorems/343d1237-df3c-4bbf-a9e2-858bf02da144
-- title:
--   Log-Determinant Trace Characterization
-- statement:
--   This is a matrix characterization used in the weak Monge–Ampère route.
--
--   Let $A$ be a positive semidefinite real $n\times n$ matrix and let $b\in\mathbb R$. Then the following are equivalent:
--
--   1. for every positive definite matrix $J$,
--   $$b+\log\det J+n\le\operatorname{tr}(JA);$$
--   2. $A$ is positive definite and $e^b\le\det A$.
--
--   The statement is finite-dimensional and purely algebraic; it expresses the logarithmic determinant as an infimum of positive-definite trace functionals.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/LogDet.lean#L110-L144 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.LogDet`, declaration `FunctionalInequalities.Analysis.forall_posDef_add_log_det_le_trace_iff`; the repository is private at upload time).

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
section LogDetInf

theorem FunctionalInequalities.Analysis.forall_posDef_add_log_det_le_trace_iff_408915f {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (b : ℝ) :
    (∀ J : Matrix (Fin n) (Fin n) ℝ, J.PosDef → b + Real.log J.det + n ≤ (J * A).trace) ↔
      (A.PosDef ∧ Real.exp b ≤ A.det) := by sorry
