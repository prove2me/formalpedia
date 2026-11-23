-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_finite_of_exact
-- name    : GroundTheory.GroupCoh.finite_of_exact
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:42.313567+00:00
-- url     : https://prove2.me/theorems/3575d156-3dea-4113-bcb8-d6ef8e81723e
-- title:
--   Group Coh: finite of exact
-- statement:
--   The Group Coh construction uses the finite of exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L11-L17

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.GroupCoh

theorem GroundTheory.GroupCoh.finite_of_exact {X Y Z : Type*} [AddGroup X] [AddGroup Y] [AddGroup Z]
    (d : X →+ Y) (e : Y →+ Z) (h : e.ker = d.range) [Finite X] [Finite Z] : Finite Y := by sorry
