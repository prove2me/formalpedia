-- Prove2me | Theorems.Thm_MIPRE_Introspection_isometricPOVM_map_mats_eq
-- name    : MIPRE.Introspection.isometricPOVM_map_mats_eq
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:25:54.800477+00:00
-- url     : https://prove2.me/theorems/40ec7537-1dcc-4dd2-82e1-14dcb39fe8f5
-- title:
--   Coarse-graining a completed image measurement is the image of the coarse-graining, with the same complement placed at the mapped default
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.IsometricCompletionError` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The cost of completing isometric image measurements. The extracted ideal state need not lie exactly in the isometries' images. Its image-complement mass is bounded by its squared distance to the actual embedded state. Completing an image PVM at one outcome therefore adds only a dimension-independent error, even when primitive estimates are stated on the ideal state.
--
--   Coarse-graining a completed image measurement is the image of the
--   coarse-graining, with the same complement placed at the mapped default.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open Matrix Finset Classical
--   open scoped Kronecker ComplexOrder MatrixOrder
--   variable {H R A B : Type*} [Fintype H] [DecidableEq H]
--
--   theorem MIPRE.Introspection.isometricPOVM_map_mats_eq (V : Matrix R H ℂ) (hV : Vᴴ * V = 1)
--       (a₀ : A) (M : POVM A H) (hM : IsPVM (fun a => (M.mats a).val)) (f : A → B) (b : B) :
--       (((isometricPOVM V hV a₀ M hM).map f).mats b).val =
--         isometricEffect V (f a₀) (fun b => ((M.map f).mats b).val) b
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.isometricPOVM_map_mats_eq` is declared in `MIPRE/Foundations/Introspection/IsometricCompletionError.lean`, lines 45–63. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/IsometricCompletionError.lean#L45-L63

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability
import Definitions.Def_MIPRE_Foundations_Introspection_IsometricStrategy

open MIPRE
open MIPRE.Introspection
open Matrix Finset Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H R A B : Type*} [Fintype H] [DecidableEq H]
  [Fintype R] [DecidableEq R] [Fintype A] [Fintype B]

theorem MIPRE.Introspection.isometricPOVM_map_mats_eq (V : Matrix R H ℂ) (hV : Vᴴ * V = 1)
    (a₀ : A) (M : POVM A H) (hM : IsPVM (fun a => (M.mats a).val)) (f : A → B) (b : B) :
    (((isometricPOVM V hV a₀ M hM).map f).mats b).val =
      isometricEffect V (f a₀) (fun b => ((M.map f).mats b).val) b := by sorry
