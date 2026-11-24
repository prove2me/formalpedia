-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_glue_closedImmersions_open_cover
-- name    : GlobalTheory.T.exists_glue_closedImmersions_open_cover
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:36:19.365378+00:00
-- url     : https://prove2.me/theorems/b12d5cb7-04ba-4cde-b140-112c9ecc8203
-- title:
--   T: exists glue closed Immersions open cover
-- statement:
--   The T construction uses the exists glue closed Immersions open cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGlueClosedImmersionsOpenCoverStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsGlueClosedImmersionsOpenCoverStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlueClosedImmersionsOpenCover
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlueClosedImmersionsOpenCoverStatement
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

theorem GlobalTheory.T.exists_glue_closedImmersions_open_cover : ∀ (X : Scheme.{0}) (ι : Type) (Xi : ι → Scheme.{0}) (m : ∀ i, Xi i ⟶ X), (∀ i, IsOpenImmersion (m i)) → (∀ x : X, ∃ i, x ∈ Set.range (m i)) → ∀ (A : ι → Scheme.{0}) (a : ∀ i, A i ⟶ Xi i), (∀ i, IsClosedImmersion (a i)) → (∀ (i j : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i) (g' : Y ⟶ Xi j), g ≫ m i = g' ≫ m j → ((∃ z : Y ⟶ A i, z ≫ a i = g) ↔ (∃ z : Y ⟶ A j, z ≫ a j = g'))) → ∃ (B : Scheme.{0}) (b : B ⟶ X), IsClosedImmersion b ∧ ∀ (i : ι) (Y : Scheme.{0}) (g : Y ⟶ Xi i), ((∃ z : Y ⟶ B, z ≫ b = g ≫ m i) ↔ (∃ z : Y ⟶ A i, z ≫ a i = g)) := by sorry
