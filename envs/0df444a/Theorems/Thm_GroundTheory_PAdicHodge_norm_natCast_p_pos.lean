-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_natCast_p_pos
-- name    : GroundTheory.PAdicHodge.norm_natCast_p_pos
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:47:19.811461+00:00
-- url     : https://prove2.me/theorems/57d604c8-2a25-4fe4-8f73-388cba6a41c3
-- title:
--   PAdic Hodge: norm nat Cast p pos
-- statement:
--   The PAdic Hodge construction uses the norm nat Cast p pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean#L51-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean#L51-L52

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

theorem GroundTheory.PAdicHodge.norm_natCast_p_pos : 0 < ‖(p : ℂ_[p])‖ := by sorry
