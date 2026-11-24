-- Prove2me | Theorems.Thm_GlobalTheory_ringHom_faithfullyFlat_comp
-- name    : GlobalTheory.ringHom_faithfullyFlat_comp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:17:28.282004+00:00
-- url     : https://prove2.me/theorems/c6915692-4112-44ee-b5f0-460a667c2e25
-- title:
--   Global Theory: ring Hom faithfully Flat comp
-- statement:
--   The Global Theory construction uses the ring Hom faithfully Flat comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L483-L486
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L483-L486

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
variable {A B A' B' : Type*} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']

theorem GlobalTheory.ringHom_faithfullyFlat_comp {f : A →+* B} {g : B →+* B'} (hf : f.FaithfullyFlat)
    (hg : g.FaithfullyFlat) : (g.comp f).FaithfullyFlat := by sorry
