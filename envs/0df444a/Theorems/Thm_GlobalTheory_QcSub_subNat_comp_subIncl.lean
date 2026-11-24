-- Prove2me | Theorems.Thm_GlobalTheory_QcSub_subNat_comp_subIncl
-- name    : GlobalTheory.QcSub.subNat_comp_subIncl
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:03:09.315425+00:00
-- url     : https://prove2.me/theorems/599dce38-4623-4b70-a850-8c67a1caee31
-- title:
--   Qc Sub: sub Nat comp sub Incl
-- statement:
--   The Qc Sub construction uses the sub Nat comp sub Incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubNatCompSubIncl.lean#L101-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubNatCompSubIncl.lean#L101-L103

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
variable {ι : Type} (V : ι → X.Opens) (T : ∀ j, Set (F.obj (op (V j))))

theorem GlobalTheory.QcSub.subNat_comp_subIncl :
    subNat F α V T ≫ subIncl F α V T = (Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α := by sorry
