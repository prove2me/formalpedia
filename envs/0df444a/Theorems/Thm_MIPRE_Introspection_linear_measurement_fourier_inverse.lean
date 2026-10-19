-- Prove2me | Theorems.Thm_MIPRE_Introspection_linear_measurement_fourier_inverse
-- name    : MIPRE.Introspection.linear_measurement_fourier_inverse
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:26:08.015352+00:00
-- url     : https://prove2.me/theorems/04571491-d204-471f-b947-6616b1ea8f13
-- title:
--   Recover the projector on a fiber by averaging only over the kernel's perpendicular
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.LinearMeasurement` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Fourier formulas for a linear-map measurement. The two identities of `lem:pauli-linear-fourier`, in characteristic two. The formulas hold for either Weyl family, and more generally for any operator family with its Fourier-defined spectral operators. Orthogonality is the actual dot product perpendicular subspace, not a canonical direct-sum complement.
--
--   Recover the projector on a fiber by averaging only over the kernel's perpendicular.
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
--   theorem MIPRE.Introspection.linear_measurement_fourier_inverse
--       (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
--       (L : (Fin n → F) →ₗ[F] (Fin n → F)) (x : Fin n → F) :
--       (Fintype.card (CL.perp L.ker) : ℂ)⁻¹ •
--         ∑ v : CL.perp L.ker, sgn (trDot v.1 x) • w v.1 = synOf w L (L x)
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.linear_measurement_fourier_inverse` is declared in `MIPRE/Foundations/Introspection/LinearMeasurement.lean`, lines 108–134. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/LinearMeasurement.lean#L108-L134; blueprint lem:pauli-linear-fourier

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

theorem MIPRE.Introspection.linear_measurement_fourier_inverse
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (x : Fin n → F) :
    (Fintype.card (CL.perp L.ker) : ℂ)⁻¹ •
      ∑ v : CL.perp L.ker, sgn (trDot v.1 x) • w v.1 = synOf w L (L x) := by sorry
