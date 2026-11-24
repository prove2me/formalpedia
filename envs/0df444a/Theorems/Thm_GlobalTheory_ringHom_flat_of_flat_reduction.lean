-- Prove2me | Theorems.Thm_GlobalTheory_ringHom_flat_of_flat_reduction
-- name    : GlobalTheory.ringHom_flat_of_flat_reduction
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:17:41.202668+00:00
-- url     : https://prove2.me/theorems/fedc67ea-4666-4d21-b7ce-d3d5dfadee83
-- title:
--   Global Theory: ring Hom flat of flat reduction
-- statement:
--   The Global Theory construction uses the ring Hom flat of flat reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L215-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L215-L227

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open IsLocalRing
variable {A B : Type*} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B]

theorem GlobalTheory.ringHom_flat_of_flat_reduction {C D : Type*} [CommRing C] [CommRing D] (φ : A →+* B)
    {π : A} (hπ : φ π ∈ Ideal.jacobson (⊥ : Ideal B)) (hreg : IsSMulRegular B (φ π))
    (p : A →+* C) (q : B →+* D) (ψ : C →+* D)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (hpπ : RingHom.ker p = Ideal.span {π}) (hqπ : RingHom.ker q = Ideal.span {φ π})
    (hsq : ψ.comp p = q.comp φ) (hψ : ψ.Flat) : φ.Flat := by sorry
