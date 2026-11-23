-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_KerModRange_map_mk
-- name    : GroundTheory.GroupCoh.KerModRange.map_mk
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:53.277465+00:00
-- url     : https://prove2.me/theorems/ad7a9c85-6011-4778-b7eb-de33d8191c5d
-- title:
--   Ker Mod Range: map mk
-- statement:
--   The Ker Mod Range construction uses the map mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L117-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean#L117-L121

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
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

theorem GroundTheory.GroupCoh.KerModRange.map_mk {fA gA : A →+ A} {fB gB : B →+ B} (i : A →+ B)
    (hf : ∀ a, i (fA a) = fB (i a)) (hg : ∀ a, i (gA a) = gB (i a)) (a : fA.ker) :
    KerModRange.map i hf hg (QuotientAddGroup.mk a : KerModRange fA gA) =
      (QuotientAddGroup.mk (kerMap i hf a) : KerModRange fB gB) := by sorry
