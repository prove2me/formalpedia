-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateRightIso_cupR
-- name    : GroundTheory.GroupCoh.tateRightIso_cupR
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:33:29.70301+00:00
-- url     : https://prove2.me/theorems/bffc06e3-8739-5581-9839-ef6bc58d1290
-- title:
--   Group Coh: tate Right Iso cup R
-- statement:
--   The Group Coh construction uses the tate Right Iso cup R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean#L127-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean#L127-L132

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_CupTateShift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable [Fintype G]

theorem GroundTheory.GroupCoh.tateRightIso_cupR {p q : ℤ} (μ : TateCupFam k G p (q + 1)) (A B : Rep.{u} k G) (r : ℤ)
    (h : p + q = r) (a : tateCohomology A p) (b : tateCohomology B q) :
    (tateRightIso A B r).hom.hom (tateCupR μ A B r h a b) =
      tsgn k p • μ A (augIdeal k G ⊗ B) (r + 1) (by omega) a ((augShiftδ B q).hom b) := by sorry
