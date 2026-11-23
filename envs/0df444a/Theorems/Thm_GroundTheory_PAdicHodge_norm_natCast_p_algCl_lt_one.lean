-- Prove2me | Theorems.Thm_GroundTheory_PAdicHodge_norm_natCast_p_algCl_lt_one
-- name    : GroundTheory.PAdicHodge.norm_natCast_p_algCl_lt_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:02.244084+00:00
-- url     : https://prove2.me/theorems/b39740d0-5451-44e6-8901-367bc13af2e3
-- title:
--   PAdic Hodge: norm nat Cast p alg Cl lt one
-- statement:
--   The PAdic Hodge construction uses the norm nat Cast p alg Cl lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/PAdicHodge/UnramifiedClosure.lean#L43-L45

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

theorem GroundTheory.PAdicHodge.norm_natCast_p_algCl_lt_one : ‖(p : PadicAlgCl p)‖ < 1 := by sorry
