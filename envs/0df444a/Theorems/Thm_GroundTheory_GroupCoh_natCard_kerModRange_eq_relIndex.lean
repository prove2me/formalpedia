-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_natCard_kerModRange_eq_relIndex
-- name    : GroundTheory.GroupCoh.natCard_kerModRange_eq_relIndex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:05.084721+00:00
-- url     : https://prove2.me/theorems/1ba66528-7a8c-4bd6-bf19-82f6070af1ab
-- title:
--   Group Coh: nat Card ker Mod Range eq rel Index
-- statement:
--   The Group Coh construction uses the nat Card ker Mod Range eq rel Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandTate.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandTate.lean#L12-L14

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandRep
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_HerbrandTate
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
universe u
open CategoryTheory

theorem GroundTheory.GroupCoh.natCard_kerModRange_eq_relIndex {A : Type*} [AddCommGroup A] (f g : A →+ A) :
    Nat.card (KerModRange f g) = g.range.relIndex f.ker := by sorry
