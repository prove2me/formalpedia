-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_quadraticFloor_of_posDef_408915f
-- name    : FunctionalInequalities.Analysis.exists_quadraticFloor_of_posDef_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:19:27.278477+00:00
-- url     : https://prove2.me/theorems/7e272362-0790-478d-9f19-e40c560099f9
-- title:
--   Positive Quadratic Floor for Positive-Definite Matrices
-- statement:
--   Let $\iota$ be a finite index type and let $S$ be a positive-definite real matrix indexed by $\iota$. Then there exists $a>0$ such that `QuadraticFloor S a` holds; equivalently, every vector $v$ satisfies
--
--   $$a\|v\|^2\le\langle v,Sv\rangle.$$
--
--   The conclusion also covers the empty index type, where the theorem supplies the explicit floor $a=1$. This is a finite-dimensional matrix positivity lemma.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Positivity.lean#L131-L145 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Positivity`, declaration `FunctionalInequalities.Analysis.exists_quadraticFloor_of_posDef`; the repository is private at upload time).

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
section Floor
open Matrix Finset
open scoped RealInnerProductSpace Matrix.Norms.L2Operator
variable [DecidableEq ι]

theorem FunctionalInequalities.Analysis.exists_quadraticFloor_of_posDef_408915f {S : Matrix ι ι ℝ} (hS : S.PosDef) :
    ∃ a : ℝ, 0 < a ∧ QuadraticFloor S a := by sorry
