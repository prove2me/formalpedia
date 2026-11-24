-- Prove2me | Theorems.Thm_GlobalTheory_exists_factor_closedImmersion_of_locally
-- name    : GlobalTheory.exists_factor_closedImmersion_of_locally
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:31:31.956107+00:00
-- url     : https://prove2.me/theorems/874f7a40-5568-4627-95aa-bab2a9e71cb3
-- title:
--   Global Theory: exists factor closed Immersion of locally
-- statement:
--   The Global Theory construction uses the exists factor closed Immersion of locally property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFactorClosedImmersionOfLocallyOnSource.lean#L7-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFactorClosedImmersionOfLocallyOnSource.lean#L7-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFactorClosedImmersionOfLocallyOnSource
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
open GlobalTheory

theorem GlobalTheory.exists_factor_closedImmersion_of_locally :
    ∀ (Z A Y : Scheme.{0}) (a : A ⟶ Z), IsClosedImmersion a → ∀ (g : Y ⟶ Z),
      (∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧ ∃ z : W.toScheme ⟶ A, z ≫ a = W.ι ≫ g) →
      ∃ z : Y ⟶ A, z ≫ a = g := by sorry
