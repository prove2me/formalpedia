-- Prove2me | Theorems.Thm_MIPRE_Introspection_subspaceTrace_eq_zero_iff
-- name    : MIPRE.Introspection.subspaceTrace_eq_zero_iff
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:25:46.211791+00:00
-- url     : https://prove2.me/theorems/98893859-78aa-4ae2-b765-e243729b9b55
-- title:
--   The trace annihilator of an F-subspace is its ordinary dot-product perpendicular
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.LinearMeasurement` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Fourier formulas for a linear-map measurement. The two identities of `lem:pauli-linear-fourier`, in characteristic two. The formulas hold for either Weyl family, and more generally for any operator family with its Fourier-defined spectral operators. Orthogonality is the actual dot product perpendicular subspace, not a canonical direct-sum complement.
--
--   The trace annihilator of an `F`-subspace is its ordinary dot-product perpendicular.
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
--   theorem MIPRE.Introspection.subspaceTrace_eq_zero_iff (S : Submodule F (Fin n → F)) (c : Fin n → F) :
--       subspaceTrace S c = 0 ↔ c ∈ CL.perp S
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.subspaceTrace_eq_zero_iff` is declared in `MIPRE/Foundations/Introspection/LinearMeasurement.lean`, lines 36–51. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/LinearMeasurement.lean#L36-L51; blueprint lem:pauli-linear-fourier

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

theorem MIPRE.Introspection.subspaceTrace_eq_zero_iff (S : Submodule F (Fin n → F)) (c : Fin n → F) :
    subspaceTrace S c = 0 ↔ c ∈ CL.perp S := by sorry
