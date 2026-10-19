-- Prove2me | Theorems.Thm_MIPRE_Introspection_conditionalIdeal_eq_coarse_of_reject
-- name    : MIPRE.Introspection.conditionalIdeal_eq_coarse_of_reject
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:14:44.606981+00:00
-- url     : https://prove2.me/theorems/98c60897-077b-4021-b34a-ca8ab93da5f2
-- title:
--   If a later PVM's prefix is selected by Q, and all rejected keyed comparisons are orthogonal, the conditional ideal product is exactly its coarse later measurement
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.ConditionalNormalizerExact` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Exact conditional products from rejected-outcome orthogonality
--
--   If a later PVM's prefix is selected by `Q`, and all rejected keyed
--   comparisons are orthogonal, the conditional ideal product is exactly its
--   coarse later measurement.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open Finset Matrix Classical
--   variable {H I O Y Z : Type*} [Fintype H] [DecidableEq H]
--
--   theorem MIPRE.Introspection.conditionalIdeal_eq_coarse_of_reject
--       (P : I → Matrix H H ℂ) (N : O → Matrix H H ℂ) (Q : Y → Matrix H H ℂ)
--       (f : Y → I → Z) (g : O → Y × Z)
--       (hP : IsPVM P) (hN : IsPVM N)
--       (hc : ∀ y i, Commute (Q y) (P i))
--       (hprefix : ∀ y o, Q y * N o = if (g o).1 = y then N o else 0)
--       (hreject : ∀ i o, f (g o).1 i ≠ (g o).2 → P i * N o = 0)
--       (p : Y × Z) : conditionalIdeal P Q f p = fibSum N g p
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.conditionalIdeal_eq_coarse_of_reject` is declared in `MIPRE/Foundations/Introspection/ConditionalNormalizerExact.lean`, lines 46–78. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/ConditionalNormalizerExact.lean#L46-L78; blueprint lem:intro-concrete-ideal-step

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

theorem MIPRE.Introspection.conditionalIdeal_eq_coarse_of_reject
    (P : I → Matrix H H ℂ) (N : O → Matrix H H ℂ) (Q : Y → Matrix H H ℂ)
    (f : Y → I → Z) (g : O → Y × Z)
    (hP : IsPVM P) (hN : IsPVM N)
    (hc : ∀ y i, Commute (Q y) (P i))
    (hprefix : ∀ y o, Q y * N o = if (g o).1 = y then N o else 0)
    (hreject : ∀ i o, f (g o).1 i ≠ (g o).2 → P i * N o = 0)
    (p : Y × Z) : conditionalIdeal P Q f p = fibSum N g p := by sorry
