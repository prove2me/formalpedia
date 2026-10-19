-- Prove2me | Theorems.Thm_MIPRE_Introspection_pauli_twirl_dist_le
-- name    : MIPRE.Introspection.pauli_twirl_dist_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:28:13.382314+00:00
-- url     : https://prove2.me/theorems/92530caf-3f71-45a2-a79b-00e1b3375258
-- title:
--   Twirling by all Z operators and kernel X operators costs four times each commutator error
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.PauliTwirlDistance` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Approximate Pauli mixing with explicit constants
--
--   Twirling by all `Z` operators and kernel `X` operators costs four times each commutator error.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open Finset Matrix MIPRE.Weyl Classical
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
--
--   theorem MIPRE.Introspection.pauli_twirl_dist_le (L : (Fin n → F) →ₗ[F] (Fin n → F))
--       (ξ : H × K → ℂ) (M : POVM A ((Fin n → F) × H)) :
--       (∑ a, stateSqNorm (eprWithAux ξ)
--         (averageX L.ker (dephaseZ (M.mats a).val) - (M.mats a).val)) ≤
--         4 * ((Fintype.card (Fin n → F) : ℝ)⁻¹ * ∑ v : Fin n → F, ∑ a,
--           stateSqNorm (eprWithAux ξ) ((M.mats a).val * aOp (wZ v) - aOp (wZ v) * (M.mats a).val)) +
--         4 * ((Fintype.card L.ker : ℝ)⁻¹ * ∑ v : L.ker, ∑ a,
--           stateSqNorm (eprWithAux ξ) ((M.mats a).val * aOp (wX v.1) - aOp (wX v.1) * (M.mats a).val))
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.pauli_twirl_dist_le` is declared in `MIPRE/Foundations/Introspection/PauliTwirlDistance.lean`, lines 39–64. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/PauliTwirlDistance.lean#L39-L64; blueprint lem:pauli-mixing-coordinates

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
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR

open MIPRE
open MIPRE.Introspection
open Finset Matrix MIPRE.Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {n : ℕ} {H K A : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] [Fintype A]

theorem MIPRE.Introspection.pauli_twirl_dist_le (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (ξ : H × K → ℂ) (M : POVM A ((Fin n → F) × H)) :
    (∑ a, stateSqNorm (eprWithAux ξ)
      (averageX L.ker (dephaseZ (M.mats a).val) - (M.mats a).val)) ≤
      4 * ((Fintype.card (Fin n → F) : ℝ)⁻¹ * ∑ v : Fin n → F, ∑ a,
        stateSqNorm (eprWithAux ξ) ((M.mats a).val * aOp (wZ v) - aOp (wZ v) * (M.mats a).val)) +
      4 * ((Fintype.card L.ker : ℝ)⁻¹ * ∑ v : L.ker, ∑ a,
        stateSqNorm (eprWithAux ξ) ((M.mats a).val * aOp (wX v.1) - aOp (wX v.1) * (M.mats a).val)) := by sorry
