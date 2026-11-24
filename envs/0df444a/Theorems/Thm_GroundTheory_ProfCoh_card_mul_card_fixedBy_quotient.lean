-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_card_mul_card_fixedBy_quotient
-- name    : GroundTheory.ProfCoh.card_mul_card_fixedBy_quotient
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:48:09.093553+00:00
-- url     : https://prove2.me/theorems/034eaa7c-f239-453c-b468-fca9d3c09ccd
-- title:
--   Prof Coh: card mul card fixed By quotient
-- statement:
--   The Prof Coh construction uses the card mul card fixed By quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/ArtinCount.lean#L24-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/GlobalEulerCharacteristic/ArtinCount.lean#L24-L34

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_ArtinCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open MulAction
variable {Γ : Type*} [Group Γ]

theorem GroundTheory.ProfCoh.card_mul_card_fixedBy_quotient [Finite Γ] (D : Subgroup Γ) (x : Γ) :
    Nat.card D * Nat.card (fixedBy (Γ ⧸ D) x) = Nat.card {y : Γ // y⁻¹ * x * y ∈ D} := by sorry
