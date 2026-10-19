-- Prove2me | Theorems.Thm_MIPRE_Introspection_linear_measurements_commute
-- name    : MIPRE.Introspection.linear_measurements_commute
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:14:04.852547+00:00
-- url     : https://prove2.me/theorems/fe7b8eda-92ca-42a8-9adc-a35d2b20d619
-- title:
--   The perpendicular-kernel inclusion makes every sampling projector commute with every hiding projector, including zero projectors at outcomes outside the ranges
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.Commutation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Commutation of the sampling and hiding measurements
--
--   The perpendicular-kernel inclusion makes every sampling projector commute with every
--   hiding projector, including zero projectors at outcomes outside the ranges.
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
--   theorem MIPRE.Introspection.linear_measurements_commute
--       (L R : (Fin n → F) →ₗ[F] (Fin n → F)) (hLR : CL.perp R.ker ≤ L.ker)
--       (a b : Fin n → F) : Commute (synOf wZ L a) (synOf wX R b)
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.linear_measurements_commute` is declared in `MIPRE/Foundations/Introspection/Commutation.lean`, lines 32–56. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/Commutation.lean#L32-L56; blueprint lem:pauli-commute-criterion

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
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
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement

open MIPRE
open MIPRE.Introspection
open Finset MIPRE.Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}

theorem MIPRE.Introspection.linear_measurements_commute
    (L R : (Fin n → F) →ₗ[F] (Fin n → F)) (hLR : CL.perp R.ker ≤ L.ker)
    (a b : Fin n → F) : Commute (synOf wZ L a) (synOf wX R b) := by sorry
