-- Prove2me | Theorems.Thm_GlobalTheory_includeRight_faithfullyFlat
-- name    : GlobalTheory.includeRight_faithfullyFlat
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:54:48.204598+00:00
-- url     : https://prove2.me/theorems/c28ca8ab-1aef-44ad-b242-7577db5505e5
-- title:
--   Global Theory: include Right faithfully Flat
-- statement:
--   The Global Theory construction uses the include Right faithfully Flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L488-L495
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L488-L495

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
variable {A B A' B' : Type*} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']

theorem GlobalTheory.includeRight_faithfullyFlat (k K B : Type*) [CommRing k] [CommRing K] [CommRing B]
    [Algebra k K] [Algebra k B] [Module.FaithfullyFlat k K] :
    ((Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B) : B →+* K ⊗[k] B).FaithfullyFlat := by sorry
