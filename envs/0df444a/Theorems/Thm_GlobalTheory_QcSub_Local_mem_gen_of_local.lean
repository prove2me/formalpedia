-- Prove2me | Theorems.Thm_GlobalTheory_QcSub_Local_mem_gen_of_local
-- name    : GlobalTheory.QcSub.Local.mem_gen_of_local
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:03:30.577222+00:00
-- url     : https://prove2.me/theorems/1c9337da-e85f-4dc8-ab6c-6dad8389adb8
-- title:
--   Local: mem gen of local
-- statement:
--   The Local construction uses the mem gen of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemAdjoinRestrictedSectionsOfLocal.lean#L55-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemAdjoinRestrictedSectionsOfLocal.lean#L55-L126

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubNatCompSubIncl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemAdjoinRestrictedSectionsOfLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
open GlobalTheory GlobalTheory.QcSub GlobalTheory.QcSub.Local

theorem GlobalTheory.QcSub.Local.mem_gen_of_local (X : Scheme.{0}) (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    (V W : X.Opens) (T : Set (F.obj (op V))) (b : F.obj (op W))
    (H : ∀ x ∈ W ⊓ V, ∃ D : X.Opens, IsAffineOpen D ∧ x ∈ D ∧ ∃ (hW : D ≤ W) (hV : D ≤ V),
      (F.map (homOfLE hW).op).hom b ∈ gen F α hV T)
    (W' : X.Opens) (hW' : IsAffineOpen W') (hW : W' ≤ W) (hV : W' ≤ V) :
    (F.map (homOfLE hW).op).hom b ∈ gen F α hV T := by sorry
