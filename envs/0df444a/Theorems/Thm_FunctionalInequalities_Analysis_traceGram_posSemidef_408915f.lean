-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_traceGram_posSemidef_408915f
-- name    : FunctionalInequalities.Analysis.traceGram_posSemidef_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:24:53.179976+00:00
-- url     : https://prove2.me/theorems/5744f01f-3976-4887-8bbd-326c5681192b
-- title:
--   Positive Semidefinite Trace Gram Matrix
-- statement:
--   This formalizes part of Theorem 2.5 of Letwin (arXiv:2607.24164v1), cited there as the key moment-map Hessian bound.
--
--   Let ι and κ be finite index types. Let B be a real positive semidefinite matrix on ι, and let Tₐ be a family of symmetric real matrices indexed by κ. Define the κ-by-κ matrix
--
--   $$G_{ab}=\operatorname{tr}(B T_a B T_b).$$
--
--   Then G is positive semidefinite.
--
--   The result provides a trace-weighted Gram-matrix formulation useful for controlling families of symmetric derivative matrices.
--
--   **Formalization Note** The statement is purely finite-dimensional and algebraic; it does not itself assert the probabilistic expectation inequality reviewed for the cited paper item.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Positivity.lean#L384-L449 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Positivity`, declaration `FunctionalInequalities.Analysis.traceGram_posSemidef`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.traceGram_posSemidef_408915f {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : Matrix ι ι ℝ) (hB : B.PosSemidef)
    (T : κ → Matrix ι ι ℝ) (hT : ∀ a, (T a).IsSymm) :
    (Matrix.of fun a b => (B * T a * B * T b).trace).PosSemidef := by sorry
