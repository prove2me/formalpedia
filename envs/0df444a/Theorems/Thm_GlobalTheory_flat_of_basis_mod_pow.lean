-- Prove2me | Theorems.Thm_GlobalTheory_flat_of_basis_mod_pow
-- name    : GlobalTheory.flat_of_basis_mod_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:56:28.232491+00:00
-- url     : https://prove2.me/theorems/528f91fe-e08f-4df4-b65c-9db6acd6d560
-- title:
--   Global Theory: flat of basis mod pow
-- statement:
--   The Global Theory construction uses the flat of basis mod pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsRegularOfSupportDimQuotientAddLengthLe.lean#L37-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsRegularOfSupportDimQuotientAddLengthLe.lean#L37-L105

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsIsRegularQuotSMulTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open RingTheory.Sequence IsLocalRing TensorProduct
open GlobalTheory
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

theorem GlobalTheory.flat_of_basis_mod_pow [IsNoetherianRing A] (B : Type*) [CommRing B] [IsNoetherianRing B]
    [Algebra A B] [Module B M] [IsScalarTower A B M] [Module.Finite B M] {I : Ideal A}
    (hI : I.map (algebraMap A B) ≤ (⊥ : Ideal B).jacobson) {S : Type*} (m : S → M)
    (hsurj : Submodule.span A (Set.range m) ⊔ I • ⊤ = ⊤)
    (hinj : ∀ (n : ℕ) (z : S →₀ A),
      Finsupp.linearCombination A m z ∈ (I ^ n • ⊤ : Submodule A M) → ∀ s, z s ∈ I ^ n) :
    Module.Flat A M := by sorry
