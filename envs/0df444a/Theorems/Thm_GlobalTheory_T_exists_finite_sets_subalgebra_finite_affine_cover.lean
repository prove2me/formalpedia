-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_finite_sets_subalgebra_finite_affine_cover
-- name    : GlobalTheory.T.exists_finite_sets_subalgebra_finite_affine_cover
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:35:38.998228+00:00
-- url     : https://prove2.me/theorems/c8ef0e5d-882c-4206-8786-0a677a395332
-- title:
--   T: exists finite sets subalgebra finite affine cover
-- statement:
--   The T construction uses the exists finite sets subalgebra finite affine cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteSetsSubalgebraFiniteAffineCoverStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteSetsSubalgebraFiniteAffineCoverStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteSetsSubalgebraFiniteAffineCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubNatCompSubIncl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffineInterFiniteBasicOpenCoverStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemAdjoinRestrictedSectionsOfLocalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteSetsSubalgebraFiniteAffineCoverStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_finite_sets_subalgebra_finite_affine_cover : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F), ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered → ∀ {ι : Type} [Finite ι] (V : ι → X.Opens), (∀ j, IsAffineOpen (V j)) → ∀ (S : ∀ j, Set (F.obj (op (V j)))), (∀ j, (S j).Finite) → ∃ T : ∀ j, Set (F.obj (op (V j))), (∀ j, (T j).Finite) ∧ ∀ i, S i ⊆ sub F α V T (V i) := by sorry
