-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_QZ_mk_surjective
-- name    : GroundTheory.ProfCoh.QZ.mk_surjective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:32.870132+00:00
-- url     : https://prove2.me/theorems/dc5bdc46-fc1d-41be-a7ee-34b25f302be8
-- title:
--   QZ: mk surjective
-- statement:
--   The QZ construction uses the mk surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/TorsionDualDefs.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/TorsionDualDefs.lean#L26-L27

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualDefs
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
open Topology
open GroundTheory.ProfCoh.QZ

theorem GroundTheory.ProfCoh.QZ.mk_surjective : Function.Surjective mk := by sorry
