-- Prove2me | Theorems.Thm_MIPRE_Introspection_conditional_coarse_overlap
-- name    : MIPRE.Introspection.conditional_coarse_overlap
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:14:17.47997+00:00
-- url     : https://prove2.me/theorems/60a03b40-4da9-46a6-89e8-28f73cd0148f
-- title:
--   Keyed coarse agreement dominates fine agreement when the ideal normalizers commute with the fine ideal PVM
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.ConditionalNormalizer` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Replacing a conditional hiding normalizer by its ideal prefix. The coarse outcome map may depend on the retained conditioning label. Positivity of the ideal commuting prefix/fine-projector products lets us retain the fine agreement without a factor depending on either outcome alphabet. The resulting replacement costs three times each of the conditional, prefix, and fine errors.
--
--   Keyed coarse agreement dominates fine agreement when the ideal normalizers
--   commute with the fine ideal PVM. All extra cross terms are positive.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open Finset Matrix Classical
--   open scoped Kronecker ComplexOrder MatrixOrder
--   variable {H K I Y Z : Type*}
--
--   theorem MIPRE.Introspection.conditional_coarse_overlap (ψ : H × K → ℂ)
--       (M : I → Matrix H H ℂ) (P : I → Matrix K K ℂ) (Q : Y → Matrix K K ℂ)
--       (f : Y → I → Z) (hM : IsPVM M) (hP : IsPVM P) (hQ : IsPVM Q)
--       (hc : ∀ y i, Commute (Q y) (P i)) :
--       (∑ i, bornProb ψ (M i) (P i)) ≤
--         ∑ p : Y × Z, bornProb ψ (fibSum M (f p.1) p.2) (conditionalIdeal P Q f p)
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.conditional_coarse_overlap` is declared in `MIPRE/Foundations/Introspection/ConditionalNormalizer.lean`, lines 65–103. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/ConditionalNormalizer.lean#L65-L103; blueprint lem:intro-conditional-normalizer

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
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {H K I Y Z : Type*}
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]

theorem MIPRE.Introspection.conditional_coarse_overlap (ψ : H × K → ℂ)
    (M : I → Matrix H H ℂ) (P : I → Matrix K K ℂ) (Q : Y → Matrix K K ℂ)
    (f : Y → I → Z) (hM : IsPVM M) (hP : IsPVM P) (hQ : IsPVM Q)
    (hc : ∀ y i, Commute (Q y) (P i)) :
    (∑ i, bornProb ψ (M i) (P i)) ≤
      ∑ p : Y × Z, bornProb ψ (fibSum M (f p.1) p.2) (conditionalIdeal P Q f p) := by sorry
