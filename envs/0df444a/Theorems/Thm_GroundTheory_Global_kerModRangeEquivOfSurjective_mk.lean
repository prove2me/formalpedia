-- Prove2me | Theorems.Thm_GroundTheory_Global_kerModRangeEquivOfSurjective_mk
-- name    : GroundTheory.Global.kerModRangeEquivOfSurjective_mk
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:56:27.154062+00:00
-- url     : https://prove2.me/theorems/bf16d480-aab5-4298-941c-931b3f39cfc4
-- title:
--   Global: ker Mod Range Equiv Of Surjective mk
-- statement:
--   The Global construction uses the ker Mod Range Equiv Of Surjective mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/CycTate.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/CycTate.lean#L20-L23

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem GroundTheory.Global.kerModRangeEquivOfSurjective_mk {f g : A →+ A} (φ : f.ker →+ B)
    (hs : Function.Surjective φ) (hk : ∀ a : f.ker, φ a = 0 ↔ (a : A) ∈ g.range) (a : f.ker) :
    kerModRangeEquivOfSurjective φ hs hk (QuotientAddGroup.mk a : KerModRange f g) = φ a := by sorry
