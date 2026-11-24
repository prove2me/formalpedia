-- Prove2me | Theorems.Thm_GlobalTheory_QcSub_map_gen_le
-- name    : GlobalTheory.QcSub.map_gen_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:03:07.941937+00:00
-- url     : https://prove2.me/theorems/625fb3db-8b87-4c8d-bd83-5e3a25dcde61
-- title:
--   Qc Sub: map gen le
-- statement:
--   The Qc Sub construction uses the map gen le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubNatCompSubIncl.lean#L20-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubNatCompSubIncl.lean#L20-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubNatCompSubIncl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Opposite
open GlobalTheory GlobalTheory.QcSub
variable {X : Scheme.{0}} (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)

theorem GlobalTheory.QcSub.map_gen_le {V W W' : X.Opens} (h : W ≤ V) (h' : W' ≤ W) (T : Set (F.obj (op V))) :
    (gen F α h T).map (F.map (homOfLE h').op).hom ≤ gen F α (h'.trans h) T := by sorry
