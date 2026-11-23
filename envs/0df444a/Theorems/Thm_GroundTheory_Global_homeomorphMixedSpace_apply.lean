-- Prove2me | Theorems.Thm_GroundTheory_Global_homeomorphMixedSpace_apply
-- name    : GroundTheory.Global.homeomorphMixedSpace_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:26.771821+00:00
-- url     : https://prove2.me/theorems/1387d45f-0215-4957-9081-b8b9733ce4c5
-- title:
--   Global: homeomorph Mixed Space apply
-- statement:
--   The Global construction uses the homeomorph Mixed Space apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/IntegersLattice.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/IntegersLattice.lean#L37-L38

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_IntegersLattice
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
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.AdeleRing
variable (K : Type*) [Field K]

theorem GroundTheory.Global.homeomorphMixedSpace_apply (x : K∞) :
    homeomorphMixedSpace K x = InfiniteAdeleRing.ringEquiv_mixedSpace K x := by sorry
