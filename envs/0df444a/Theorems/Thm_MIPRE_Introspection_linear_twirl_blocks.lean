-- Prove2me | Theorems.Thm_MIPRE_Introspection_linear_twirl_blocks
-- name    : MIPRE.Introspection.linear_twirl_blocks
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:14:09.950539+00:00
-- url     : https://prove2.me/theorems/3aba31b9-8fed-4aab-b815-20ae9ab98b60
-- title:
--   The exact block decomposition used by the hiding argument, including an arbitrary ancilla
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.BlockTwirl` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Entry formulas for Pauli twirls with an ancillary space
--
--   The exact block decomposition used by the hiding argument, including an arbitrary ancilla.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open Finset MIPRE.Weyl Classical Matrix Kronecker
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
--   variable {n : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
--
--   theorem MIPRE.Introspection.linear_twirl_blocks (L : (Fin n → F) →ₗ[F] (Fin n → F))
--       (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
--       averageX L.ker (dephaseZ M) =
--         ∑ a : Fin n → F, synOf wZ L a ⊗ₖ averagedBlock L.ker M (linearPreimage L a)
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.linear_twirl_blocks` is declared in `MIPRE/Foundations/Introspection/BlockTwirl.lean`, lines 148–163. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/BlockTwirl.lean#L148-L163; blueprint lem:pauli-linear-mixing

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
import Mathlib.LinearAlgebra.Matrix.Kronecker
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
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl

open MIPRE
open MIPRE.Introspection
open Finset MIPRE.Weyl Classical Matrix Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {H : Type*} [Fintype H] [DecidableEq H]

theorem MIPRE.Introspection.linear_twirl_blocks (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    averageX L.ker (dephaseZ M) =
      ∑ a : Fin n → F, synOf wZ L a ⊗ₖ averagedBlock L.ker M (linearPreimage L a) := by sorry
