-- Prove2me | Theorems.Thm_MIPRE_Introspection_linear_measurement_isPVM
-- name    : MIPRE.Introspection.linear_measurement_isPVM
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:26:17.60724+00:00
-- url     : https://prove2.me/theorems/8a2d11d2-a7cc-4394-919b-1ad74435774f
-- title:
--   Reading any linear map of a Weyl eigenbasis outcome is a projective measurement
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.Measurements` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Projective sampling and joint hiding measurements
--
--   Reading any linear map of a Weyl eigenbasis outcome is a projective measurement.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open Finset MIPRE.Weyl Classical
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
--   variable {n : ℕ}
--
--   theorem MIPRE.Introspection.linear_measurement_isPVM
--       (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ) (hw : IsWeylFamily w)
--       (L : (Fin n → F) →ₗ[F] (Fin n → F)) : IsPVM (synOf w L)
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.linear_measurement_isPVM` is declared in `MIPRE/Foundations/Introspection/Measurements.lean`, lines 26–30. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/Measurements.lean#L26-L30; blueprint lem:intro-linear-readout-projectivity

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement

open MIPRE
open MIPRE.Introspection
open Finset MIPRE.Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}

theorem MIPRE.Introspection.linear_measurement_isPVM
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ) (hw : IsWeylFamily w)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) : IsPVM (synOf w L) := by sorry
