-- Prove2me | Theorems.Thm_GlobalTheory_PrimaryCharacter_exists_extend_of_injective
-- name    : GlobalTheory.PrimaryCharacter.exists_extend_of_injective
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:53:35.103266+00:00
-- url     : https://prove2.me/theorems/72cbe1b7-9c2a-4d74-918e-3be9178fbe1f
-- title:
--   Primary Character: exists extend of injective
-- statement:
--   The Primary Character construction uses the exists extend of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsGeneratingCharacters.lean#L6-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsGeneratingCharacters.lean#L6-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsExtensionCharacter
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsGeneratingCharacters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PrimaryCharacter

theorem GlobalTheory.PrimaryCharacter.exists_extend_of_injective {H M F : Type} [CommGroup H] [CommGroup M] [Field F] [IsAlgClosed F]
    (Φ : H →* M) (hΦ : Function.Injective Φ) (χ : H →* Fˣ) : ∃ κ : M →* Fˣ, ∀ x, κ (Φ x) = χ x := by sorry
