-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_pow_sub_pow_le
-- name    : GroundTheory.PAdicHodge.norm_pow_sub_pow_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:57.40099+00:00
-- url     : https://prove2.me/theorems/fc3180fa-dab8-45a2-b756-ea2a99879091
-- title:
--   PAdic Hodge: norm pow sub pow le
-- statement:
--   The PAdic Hodge construction uses the norm pow sub pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean#L118-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean#L118-L125

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

theorem GroundTheory.PAdicHodge.norm_pow_sub_pow_le {a b : F} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    ‖a ^ n - b ^ n‖ ≤ ‖a - b‖ := by sorry
