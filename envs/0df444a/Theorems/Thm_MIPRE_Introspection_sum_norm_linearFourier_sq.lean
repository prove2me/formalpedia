-- Prove2me | Theorems.Thm_MIPRE_Introspection_sum_norm_linearFourier_sq
-- name    : MIPRE.Introspection.sum_norm_linearFourier_sq
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:14:05.226412+00:00
-- url     : https://prove2.me/theorems/5fc380a7-3531-4924-ad1e-23388c25fab1
-- title:
--   Parseval for vector families supported on the range of a linear map
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.CommutatorParseval` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Parseval for commutators with linear-map readouts. The character transform on the kernel's perpendicular identifies the outcome-summed commutator error of a linear-map measurement with the uniformly averaged error of its Pauli observables. This proves the characteristic-two form of the paper's `lem:W`. The identity holds on every state, with ancillary spaces and empty fibres allowed.
--
--   Parseval for vector families supported on the range of a linear map.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open Finset MIPRE.Weyl Matrix Classical
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
--   variable {n : ℕ} {N : Type*} [Fintype N]
--
--   theorem MIPRE.Introspection.sum_norm_linearFourier_sq
--       (L : (Fin n → F) →ₗ[F] (Fin n → F)) (T : (Fin n → F) → (N → ℂ))
--       (hT : ∀ y, y ∉ L.range → T y = 0) :
--       (Fintype.card (CL.perp L.ker) : ℝ)⁻¹ *
--           (∑ v : CL.perp L.ker, ‖evec (∑ y : Fin n → F,
--             sgn (trDot v.1 (linearPreimage L y)) • T y)‖ ^ 2) =
--         ∑ y : Fin n → F, ‖evec (T y)‖ ^ 2
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.sum_norm_linearFourier_sq` is declared in `MIPRE/Foundations/Introspection/CommutatorParseval.lean`, lines 44–98. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/CommutatorParseval.lean#L44-L98; blueprint lem:pauli-commutator-transfer

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
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval

open MIPRE
open MIPRE.Introspection
open Finset MIPRE.Weyl Matrix Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {N : Type*} [Fintype N]

theorem MIPRE.Introspection.sum_norm_linearFourier_sq
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (T : (Fin n → F) → (N → ℂ))
    (hT : ∀ y, y ∉ L.range → T y = 0) :
    (Fintype.card (CL.perp L.ker) : ℝ)⁻¹ *
        (∑ v : CL.perp L.ker, ‖evec (∑ y : Fin n → F,
          sgn (trDot v.1 (linearPreimage L y)) • T y)‖ ^ 2) =
      ∑ y : Fin n → F, ‖evec (T y)‖ ^ 2 := by sorry
