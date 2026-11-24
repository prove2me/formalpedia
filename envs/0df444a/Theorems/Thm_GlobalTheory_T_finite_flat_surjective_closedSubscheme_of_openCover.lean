-- Prove2me | Theorems.Thm_GlobalTheory_T_finite_flat_surjective_closedSubscheme_of_openCover
-- name    : GlobalTheory.T.finite_flat_surjective_closedSubscheme_of_openCover
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:39:23.914532+00:00
-- url     : https://prove2.me/theorems/d9193d25-de2c-4283-96a3-bdd3dd9aa2dc
-- title:
--   T: finite flat surjective closed Subscheme of open Cover
-- statement:
--   The T construction uses the finite flat surjective closed Subscheme of open Cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteFlatSurjectiveClosedSubschemeOfOpenCoverStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FiniteFlatSurjectiveClosedSubschemeOfOpenCoverStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteFlatSurjectiveClosedSubschemeOfOpenCover
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteFlatSurjectiveClosedSubschemeOfOpenCoverStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finite_flat_surjective_closedSubscheme_of_openCover : ∀ (X T₀ : Scheme.{0}) (p : X ⟶ T₀) (ι : Type) (V : ι → T₀.Opens), iSup V = ⊤ → ∀ (Xi : ι → Scheme.{0}) (m : ∀ i, Xi i ⟶ X) (q : ∀ i, Xi i ⟶ (V i).toScheme), (∀ i, IsPullback (m i) (q i) p (V i).ι) → ∀ (B : Scheme.{0}) (b : B ⟶ X), IsClosedImmersion b → ∀ (A : ι → Scheme.{0}) (a : ∀ i, A i ⟶ Xi i), (∀ i, IsClosedImmersion (a i)) → (∀ (i : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i), (∃ z : Y ⟶ B, z ≫ b = g ≫ m i) ↔ (∃ z : Y ⟶ A i, z ≫ a i = g)) → (∀ i, IsFinite (a i ≫ q i) ∧ Flat (a i ≫ q i) ∧ Surjective (a i ≫ q i)) → IsFinite (b ≫ p) ∧ Flat (b ≫ p) ∧ Surjective (b ≫ p) := by sorry
