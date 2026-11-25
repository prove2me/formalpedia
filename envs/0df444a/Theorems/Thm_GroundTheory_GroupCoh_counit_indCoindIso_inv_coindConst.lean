-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_counit_indCoindIso_inv_coindConst
-- name    : GroundTheory.GroupCoh.counit_indCoindIso_inv_coindConst
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:55:24.634359+00:00
-- url     : https://prove2.me/theorems/d2c16ecb-e341-44b8-85a3-7cb812ce31ac
-- title:
--   Group Coh: counit ind Coind Iso inv coind Const
-- statement:
--   The Group Coh construction uses the counit ind Coind Iso inv coind Const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCoresZero.lean#L127-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCoresZero.lean#L127-L141

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CoresRes
import Definitions.Def_GroundTheory_TateCohomology_TateZeroClass
import Definitions.Def_GroundTheory_TateCohomology_ResCoresZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G] (S : Subgroup G) [Fintype S]
omit [Fintype S]

theorem GroundTheory.GroupCoh.counit_indCoindIso_inv_coindConst [DecidableRel (QuotientGroup.rightRel S)]
    (A : Rep.{u} k G) (y : (res S.subtype A).ρ.invariants) :
    ((Rep.indResAdjunction.{u} k S.subtype).counit.app A).hom
      ((indCoindIso (res S.subtype A)).inv.hom (coindConst S (res S.subtype A) y)) =
      transferSum S y := by sorry
