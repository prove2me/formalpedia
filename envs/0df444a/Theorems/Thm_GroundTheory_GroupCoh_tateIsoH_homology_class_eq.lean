-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateIsoH_homology_class_eq
-- name    : GroundTheory.GroupCoh.tateIsoH_homology_class_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:14:30.42465+00:00
-- url     : https://prove2.me/theorems/03e92d02-80d5-4a16-aca6-3558900a8b0d
-- title:
--   Group Coh: tate Iso H homology class eq
-- statement:
--   The Group Coh construction uses the tate Iso H homology class eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateConnecting.lean#L26-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateConnecting.lean#L26-L40

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
set_option backward.isDefEq.respectTransparency false

theorem GroundTheory.GroupCoh.tateIsoH_homology_class_eq (A : Rep k G) (n : ℕ) [NeZero n] :
    ∃ C : (tateComplex A).cycles n ⟶ cocycles A n,
      (tateComplex A).homologyπ n ≫ (tateIsoH A n n rfl).hom = C ≫ π A n ∧
        C ≫ iCocycles A n = (tateComplex A).iCycles n := by sorry
