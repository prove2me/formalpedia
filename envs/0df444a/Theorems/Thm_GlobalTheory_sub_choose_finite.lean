-- Prove2me | Theorems.Thm_GlobalTheory_sub_choose_finite
-- name    : GlobalTheory.sub_choose_finite
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:21:38.677889+00:00
-- url     : https://prove2.me/theorems/d40d92f6-e97f-4757-bf36-933295174e1b
-- title:
--   Global Theory: sub choose finite
-- statement:
--   The Global Theory construction uses the sub choose finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteSetsSubalgebraFiniteAffineCover.lean#L44-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteSetsSubalgebraFiniteAffineCover.lean#L44-L68

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubNatCompSubIncl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffineInterFiniteBasicOpenCoverStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemAdjoinRestrictedSectionsOfLocalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteSetsSubalgebraFiniteAffineCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

theorem GlobalTheory.sub_choose_finite : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} [Finite ι] (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → ∀ (S : ∀ j, Set (F.obj (op (V j)))), (∀ j, (S j).Finite) → ∃ T : ∀ j, Set (F.obj (op (V j))), (∀ j, (T j).Finite) ∧ ∀ i, S i ⊆ sub F α V T (V i) := by sorry
