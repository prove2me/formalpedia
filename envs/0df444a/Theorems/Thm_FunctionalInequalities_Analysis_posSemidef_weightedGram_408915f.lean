-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_posSemidef_weightedGram_408915f
-- name    : FunctionalInequalities.Analysis.posSemidef_weightedGram_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:24:54.624979+00:00
-- url     : https://prove2.me/theorems/2d97bc09-7aef-4ebd-9d57-ca5dc84d7642
-- title:
--   Positive Semidefinite Weighted Gram Matrix
-- statement:
--   This statement establishes positivity of a weighted Gram matrix.
--
--   Let ι and κ be finite index types, let A be a real matrix on ι, and assume A is positive semidefinite. For an arbitrary family of real matrices Tᵢ indexed by κ, define G by
--
--   $$G_{ij}=\sum_{a,b,c,d}A_{ac}A_{bd}(T_i)_{ab}(T_j)_{cd}.$$
--
--   Then G is positive semidefinite. Equivalently, this is the matrix representation of F(A ⊗ A)Fᵀ, where F records the entries of the matrices Tᵢ.
--
--   This is a reusable finite-dimensional Gram-matrix construction for tensor and trace-energy estimates.
--
--   **Formalization Note** The matrix `Matrix.PosSemidef` and all sums range over finite types; no symmetry or definiteness beyond positive semidefiniteness of A is assumed.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Positivity.lean#L45-L70 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Positivity`, declaration `FunctionalInequalities.Analysis.posSemidef_weightedGram`; the repository is private at upload time).

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
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem FunctionalInequalities.Analysis.posSemidef_weightedGram_408915f (A : Matrix ι ι ℝ) (hA : A.PosSemidef)
    (T : κ → Matrix ι ι ℝ) :
    (Matrix.of fun i j => ∑ a, ∑ b, ∑ c, ∑ d,
      A a c * A b d * T i a b * T j c d).PosSemidef := by sorry
