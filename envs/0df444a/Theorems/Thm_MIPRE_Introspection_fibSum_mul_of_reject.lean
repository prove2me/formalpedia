-- Prove2me | Theorems.Thm_MIPRE_Introspection_fibSum_mul_of_reject
-- name    : MIPRE.Introspection.fibSum_mul_of_reject
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:14:39.284025+00:00
-- url     : https://prove2.me/theorems/78f19143-3d43-462f-9dec-0106f5855538
-- title:
--   A complete family restricted to its only possible coarse outcome acts as the identity on a compatible projector
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.ConditionalNormalizerExact` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Exact conditional products from rejected-outcome orthogonality
--
--   A complete family restricted to its only possible coarse outcome acts as
--   the identity on a compatible projector.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open Finset Matrix Classical
--   variable {H I O Y Z : Type*} [Fintype H] [DecidableEq H]
--
--   theorem MIPRE.Introspection.fibSum_mul_of_reject (P : I → Matrix H H ℂ) (R : Matrix H H ℂ)
--       (hP : ∑ i, P i = 1) (f : I → Z) (z₀ : Z)
--       (hzero : ∀ i, f i ≠ z₀ → P i * R = 0) (z : Z) :
--       fibSum P f z * R = if z = z₀ then R else 0
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.fibSum_mul_of_reject` is declared in `MIPRE/Foundations/Introspection/ConditionalNormalizerExact.lean`, lines 21–44. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/ConditionalNormalizerExact.lean#L21-L44

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
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
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
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_ConditionalNormalizer

open MIPRE
open MIPRE.Introspection
open Finset Matrix Classical
set_option linter.unusedSectionVars false
variable {H I O Y Z : Type*} [Fintype H] [DecidableEq H]
  [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
  [Fintype Y] [DecidableEq Y] [Fintype Z] [DecidableEq Z]

theorem MIPRE.Introspection.fibSum_mul_of_reject (P : I → Matrix H H ℂ) (R : Matrix H H ℂ)
    (hP : ∑ i, P i = 1) (f : I → Z) (z₀ : Z)
    (hzero : ∀ i, f i ≠ z₀ → P i * R = 0) (z : Z) :
    fibSum P f z * R = if z = z₀ then R else 0 := by sorry
