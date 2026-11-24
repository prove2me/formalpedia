-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_pow_pow_sub_pow_pow_le
-- name    : GroundTheory.PAdicHodge.norm_pow_pow_sub_pow_pow_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:48:19.127579+00:00
-- url     : https://prove2.me/theorems/ba935e95-458d-4baa-b487-1516e14aa368
-- title:
--   PAdic Hodge: norm pow pow sub pow pow le
-- statement:
--   The PAdic Hodge construction uses the norm pow pow sub pow pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean#L156-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean#L156-L164

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_GaloisOnCp
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnramifiedClosureCountableNeighbourhoods
import Definitions.Def_GroundTheory_PAdicHodge_UnramifiedClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Polynomial Filter Topology
variable (p : ℕ) [hp : Fact p.Prime]
variable {p}
variable {F : Type*} [NormedField F] [IsUltrametricDist F]
omit hp

theorem GroundTheory.PAdicHodge.norm_pow_pow_sub_pow_pow_le {a b : F} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hp1 : ‖(p : F)‖ ≤ 1)
    {e : ℕ} (he : 1 ≤ e) (hab : ‖a - b‖ ≤ ‖(p : F)‖ ^ e) (r : ℕ) :
    ‖a ^ p ^ r - b ^ p ^ r‖ ≤ ‖(p : F)‖ ^ (e + r) := by sorry
