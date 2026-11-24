-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EichlerTransf_eichler_of_involution
-- name    : GlobalTheory.CompanionTheory.EichlerTransf.eichler_of_involution
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:56:57.688488+00:00
-- url     : https://prove2.me/theorems/1c372998-c6fd-4bd4-8047-4e369bf34084
-- title:
--   Eichler Transf: eichler of involution
-- statement:
--   The Eichler Transf construction uses the eichler of involution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExtendByZeroApplyOfNe.lean#L112-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExtendByZeroApplyOfNe.lean#L112-L294

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExtendByZeroApplyOfNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EichlerTransf
open scoped ComplexOrder
variable {n m : ℕ}

theorem GlobalTheory.CompanionTheory.EichlerTransf.eichler_of_involution (J : Matrix (Fin n) (Fin n) ℂ) (hJJ : J * J = 1) (hJh : Jᴴ = J)
    (x y : Matrix (Fin n) (Fin m) ℂ) (A : Set (Fin m))
    (hxx : xᴴ * J * x = 0) (hxy : xᴴ * J * y = 1) :
    ∃ (u : Matrix (Fin m) (Fin n) ℂ) (w : Matrix (Fin n) (Fin m) ℂ), (∀ i v, i ∉ A → u i v = 0) ∧
      (∀ v i, i ∉ A → w v i = 0) ∧ (∀ i j, j ∈ A → (u * x) i j = 0) ∧
      1 + x * u + w * xᴴ * J ∈ Formalism.QuantumDeterminants.UH J ∧
      ∀ v ∈ Submodule.span ℂ (Set.range (fun i : A => (1 + x * u + w * xᴴ * J) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (1 + x * u + w * xᴴ * J) *ᵥ fun j => y j i)),
        J *ᵥ v ∈ Submodule.span ℂ (Set.range (fun i : A => (1 + x * u + w * xᴴ * J) *ᵥ fun j => x j i) ∪
          Set.range (fun i : A => (1 + x * u + w * xᴴ * J) *ᵥ fun j => y j i)) := by sorry
