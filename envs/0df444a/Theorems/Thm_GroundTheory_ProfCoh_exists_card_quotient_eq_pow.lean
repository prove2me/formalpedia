-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_exists_card_quotient_eq_pow
-- name    : GroundTheory.ProfCoh.exists_card_quotient_eq_pow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:02:18.150363+00:00
-- url     : https://prove2.me/theorems/ad2057d4-652b-5c92-b258-7f691384b2c6
-- title:
--   Prof Coh: exists card quotient eq pow
-- statement:
--   The Prof Coh construction uses the exists card quotient eq pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L210-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalEulerCharacteristic/ModNEquivOfSurjectiveApplyModNRep.lean#L210-L226

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
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
universe u
open GroundTheory.LocalField ValuativeRel IsLocalRing
variable {E : Type*} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  {p : ℕ}
variable [Fact p.Prime]

theorem GroundTheory.ProfCoh.exists_card_quotient_eq_pow (hp0 : (p : E) ≠ 0) :
    ∃ n, Nat.card (𝒪[E] ⧸ Ideal.span {(p : 𝒪[E])}) = p ^ n := by sorry
