-- Prove2me | Theorems.Thm_GlobalTheory_QcSub_subIncl_injective
-- name    : GlobalTheory.QcSub.subIncl_injective
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:03:12.387802+00:00
-- url     : https://prove2.me/theorems/c2089ef9-41a5-4d0c-8679-38bb40c66cf1
-- title:
--   Qc Sub: sub Incl injective
-- statement:
--   The Qc Sub construction uses the sub Incl injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubNatCompSubIncl.lean#L105-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SubNatCompSubIncl.lean#L105-L106

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

theorem GlobalTheory.QcSub.subIncl_injective (W : X.AffineZariskiSiteᵒᵖ) : Function.Injective ((subIncl F α V T).app W).hom := by sorry
