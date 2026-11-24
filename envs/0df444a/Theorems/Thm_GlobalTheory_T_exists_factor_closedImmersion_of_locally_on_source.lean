-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_factor_closedImmersion_of_locally_on_source
-- name    : GlobalTheory.T.exists_factor_closedImmersion_of_locally_on_source
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:35:44.654796+00:00
-- url     : https://prove2.me/theorems/a8fbe70b-fc1c-4275-bcf8-dd302846a518
-- title:
--   T: exists factor closed Immersion of locally on source
-- statement:
--   The T construction uses the exists factor closed Immersion of locally on source property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFactorClosedImmersionOfLocallyOnSourceStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFactorClosedImmersionOfLocallyOnSourceStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFactorClosedImmersionOfLocallyOnSource
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFactorClosedImmersionOfLocallyOnSourceStatement
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

theorem GlobalTheory.T.exists_factor_closedImmersion_of_locally_on_source : ∀ (Z A Y : Scheme.{0}) (a : A ⟶ Z), IsClosedImmersion a → ∀ (g : Y ⟶ Z), (∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧ ∃ z : W.toScheme ⟶ A, z ≫ a = W.ι ≫ g) → ∃ z : Y ⟶ A, z ≫ a = g := by sorry
