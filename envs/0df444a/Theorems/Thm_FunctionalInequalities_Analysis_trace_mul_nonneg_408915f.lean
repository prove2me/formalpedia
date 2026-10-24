-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_trace_mul_nonneg_408915f
-- name    : FunctionalInequalities.Analysis.trace_mul_nonneg_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:24:53.309402+00:00
-- url     : https://prove2.me/theorems/d321cbb3-a137-48b5-be9b-1e806f92cba7
-- title:
--   Nonnegative Trace Of A Product
-- statement:
--   This formalizes part of Theorem 2.5 of Letwin (arXiv:2607.24164v1), cited there as the key moment-map Hessian bound.
--
--   Let ι be a finite index type, and let A and C be real positive semidefinite matrices indexed by ι. Then the trace of their product is nonnegative:
--
--   $$0\leq \operatorname{tr}(AC).$$
--
--   The product AC itself is not asserted to be positive semidefinite.
--
--   This elementary trace-pairing fact is reusable whenever two positive semidefinite matrix fields produce a cross term.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Positivity.lean#L364-L382 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Positivity`, declaration `FunctionalInequalities.Analysis.trace_mul_nonneg`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.LinearAlgebra.Matrix.Kronecker

noncomputable section
open scoped MatrixOrder Kronecker
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section TraceGram
open scoped BigOperators Kronecker
open Matrix
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.trace_mul_nonneg_408915f {ι : Type*} [Fintype ι]
    {A C : Matrix ι ι ℝ} (hA : A.PosSemidef) (hC : C.PosSemidef) :
    0 ≤ (A * C).trace := by sorry
