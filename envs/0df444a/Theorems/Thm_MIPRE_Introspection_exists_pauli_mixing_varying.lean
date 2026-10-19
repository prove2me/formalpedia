-- Prove2me | Theorems.Thm_MIPRE_Introspection_exists_pauli_mixing_varying
-- name    : MIPRE.Introspection.exists_pauli_mixing_varying
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:41:36.938981+00:00
-- url     : https://prove2.me/theorems/2235fdaa-d6f0-4ec5-9f44-3a7318721b56
-- title:
--   Averaged mixing when the retained register and its complement vary with the question
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.VaryingPauliMixing` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Pauli mixing in question-dependent coordinate presentations. The number of sampled coordinates and both ancillary spaces can depend on the question. This is the form used after splitting a retained register from its complement. The register's ambient embeddings are not part of this statement.
--
--   Averaged mixing when the retained register and its complement vary with the question.
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
--   theorem MIPRE.Introspection.exists_pauli_mixing_varying
--       (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD1 : ∑ x, D x = 1)
--       (L : (x : X) → (Fin (n x) → F) →ₗ[F] (Fin (n x) → F))
--       (ξ : (x : X) → H x × K x → ℂ) (hξ : ∀ x, ‖evec (ξ x)‖ = 1)
--       (M : (x : X) → POVM ((Fin (n x) → F) × A) ((Fin (n x) → F) × H x))
--       (hM : ∀ x, IsPVM (fun p => ((M x).mats p).val))
--       {δ : ℝ} (hδ : ∑ x, D x * mixingError (L x) (ξ x) (M x) ≤ δ) :
--       ∃ Q : (x : X) → (Fin (n x) → F) → POVM A (H x),
--         (∑ x, D x * ∑ p : (Fin (n x) → F) × A, stateSqNorm (eprWithAux (ξ x))
--           (((M x).mats p).val - synOf wZ (L x) p.1 ⊗ₖ ((Q x p.1).mats p.2).val)) ≤
--         2 * δ + 4 * Real.sqrt δ
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.exists_pauli_mixing_varying` is declared in `MIPRE/Foundations/Introspection/VaryingPauliMixing.lean`, lines 27–52. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/VaryingPauliMixing.lean#L27-L52; blueprint lem:pauli-mixing-coordinates

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
  {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
  {n : X → ℕ} {H K : X → Type*}
  [∀ x, Fintype (H x)] [∀ x, DecidableEq (H x)]
  [∀ x, Fintype (K x)] [∀ x, DecidableEq (K x)]

theorem MIPRE.Introspection.exists_pauli_mixing_varying
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD1 : ∑ x, D x = 1)
    (L : (x : X) → (Fin (n x) → F) →ₗ[F] (Fin (n x) → F))
    (ξ : (x : X) → H x × K x → ℂ) (hξ : ∀ x, ‖evec (ξ x)‖ = 1)
    (M : (x : X) → POVM ((Fin (n x) → F) × A) ((Fin (n x) → F) × H x))
    (hM : ∀ x, IsPVM (fun p => ((M x).mats p).val))
    {δ : ℝ} (hδ : ∑ x, D x * mixingError (L x) (ξ x) (M x) ≤ δ) :
    ∃ Q : (x : X) → (Fin (n x) → F) → POVM A (H x),
      (∑ x, D x * ∑ p : (Fin (n x) → F) × A, stateSqNorm (eprWithAux (ξ x))
        (((M x).mats p).val - synOf wZ (L x) p.1 ⊗ₖ ((Q x p.1).mats p.2).val)) ≤
      2 * δ + 4 * Real.sqrt δ := by sorry
