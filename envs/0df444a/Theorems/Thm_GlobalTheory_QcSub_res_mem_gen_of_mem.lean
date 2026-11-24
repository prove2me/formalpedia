-- Prove2me | Theorems.Thm_GlobalTheory_QcSub_res_mem_gen_of_mem
-- name    : GlobalTheory.QcSub.res_mem_gen_of_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:02:59.819611+00:00
-- url     : https://prove2.me/theorems/8d6cfc1d-5bf7-4534-9d76-8990b0a148d5
-- title:
--   Qc Sub: res mem gen of mem
-- statement:
--   The Qc Sub construction uses the res mem gen of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubNatCompSubIncl.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubNatCompSubIncl.lean#L31-L34

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

theorem GlobalTheory.QcSub.res_mem_gen_of_mem {V W W' : X.Opens} (h : W ≤ V) (h' : W' ≤ W) (T : Set (F.obj (op V)))
    {b : F.obj (op W)} (hb : b ∈ gen F α h T) :
    (F.map (homOfLE h').op).hom b ∈ gen F α (h'.trans h) T := by sorry
