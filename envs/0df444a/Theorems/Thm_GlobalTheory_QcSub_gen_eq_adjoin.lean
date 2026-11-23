-- Prove2me | Theorems.Thm_GlobalTheory_QcSub_gen_eq_adjoin
-- name    : GlobalTheory.QcSub.gen_eq_adjoin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:49.246375+00:00
-- url     : https://prove2.me/theorems/f4411e0f-895a-41a4-b6cb-a96342ab3207
-- title:
--   Qc Sub: gen eq adjoin
-- statement:
--   The Qc Sub construction uses the gen eq adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubNatCompSubIncl.lean#L36-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubNatCompSubIncl.lean#L36-L41

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

theorem GlobalTheory.QcSub.gen_eq_adjoin {V W : X.Opens} (h : W ≤ V) (T : Set (F.obj (op V))) :
    letI := (α.app (op W)).hom.toAlgebra
    gen F α h T = (Algebra.adjoin Γ(X, W) ((F.map (homOfLE h).op).hom '' T)).toSubring := by sorry
