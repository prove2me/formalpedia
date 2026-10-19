-- Prove2me | Theorems.Thm_MIPRE_Introspection_exists_pauli_mixing
-- name    : MIPRE.Introspection.exists_pauli_mixing
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:26:53.814289+00:00
-- url     : https://prove2.me/theorems/2fdbe634-3393-48bd-a47c-31cede8c7603
-- title:
--   Pauli mixing produces normalized POVMs on the ancilla at every retained fibre
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.PauliMixing` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Pauli mixing with a retained classical fibre. The sampled register has a fixed coordinate presentation, with arbitrary auxiliary systems. The output consists of actual ancillary POVMs. Consistency and the two readout commutator errors control the squared state distance by an explicit square-root estimate.
--
--   Pauli mixing produces normalized POVMs on the ancilla at every retained fibre.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open Finset Matrix MIPRE.Weyl Classical
--   open scoped Kronecker
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
--
--   theorem MIPRE.Introspection.exists_pauli_mixing (L : (Fin n → F) →ₗ[F] (Fin n → F))
--       (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1)
--       (M : POVM ((Fin n → F) × A) ((Fin n → F) × H))
--       (hM : IsPVM (fun p => (M.mats p).val)) :
--       ∃ Q : (Fin n → F) → POVM A H,
--         (∑ p : (Fin n → F) × A, stateSqNorm (eprWithAux ξ)
--           ((M.mats p).val - synOf wZ L p.1 ⊗ₖ ((Q p.1).mats p.2).val)) ≤
--         2 * mixingError L ξ M + 4 * Real.sqrt (mixingError L ξ M)
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.exists_pauli_mixing` is declared in `MIPRE/Foundations/Introspection/PauliMixing.lean`, lines 54–87. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/PauliMixing.lean#L54-L87; blueprint lem:pauli-mixing-coordinates

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
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing

open MIPRE
open MIPRE.Introspection
open Finset Matrix MIPRE.Weyl Classical
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {n : ℕ} {H K A : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A]

theorem MIPRE.Introspection.exists_pauli_mixing (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (ξ : H × K → ℂ) (hξ : ‖evec ξ‖ = 1)
    (M : POVM ((Fin n → F) × A) ((Fin n → F) × H))
    (hM : IsPVM (fun p => (M.mats p).val)) :
    ∃ Q : (Fin n → F) → POVM A H,
      (∑ p : (Fin n → F) × A, stateSqNorm (eprWithAux ξ)
        ((M.mats p).val - synOf wZ L p.1 ⊗ₖ ((Q p.1).mats p.2).val)) ≤
      2 * mixingError L ξ M + 4 * Real.sqrt (mixingError L ξ M) := by sorry
