-- Prove2me | Theorems.Thm_GlobalTheory_ringHom_injective_of_surjective
-- name    : GlobalTheory.ringHom_injective_of_surjective
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:18:48.219797+00:00
-- url     : https://prove2.me/theorems/98fd6f1c-4862-46a0-becc-2e7bb55421f4
-- title:
--   Global Theory: ring Hom injective of surjective
-- statement:
--   The Global Theory construction uses the ring Hom injective of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L289-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L289-L304

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
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
variable {A : Type*} [CommRing A]

theorem GlobalTheory.ringHom_injective_of_surjective [IsNoetherianRing A] (φ : A →+* A)
    (hφ : Function.Surjective φ) : Function.Injective φ := by sorry
