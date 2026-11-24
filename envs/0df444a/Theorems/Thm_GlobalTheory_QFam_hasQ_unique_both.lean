-- Prove2me | Theorems.Thm_GlobalTheory_QFam_hasQ_unique_both
-- name    : GlobalTheory.QFam.hasQ_unique_both
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:59:22.359808+00:00
-- url     : https://prove2.me/theorems/401587c4-4127-404c-b655-66de8e541155
-- title:
--   QFam: has Q unique both
-- statement:
--   The QFam construction uses the has Q unique both property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQExpansionOfLevelCoeffAndFunctionUnique.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasQExpansionOfLevelCoeffAndFunctionUnique.lean#L26-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelCoeffAndFunctionUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open GlobalTheory GlobalTheory.QFam

theorem GlobalTheory.QFam.hasQ_unique_both :
    (∀ (N : ℕ) (f : ℍ → ℂ) (a b : ℕ → ℂ), 0 < N → HasQ N f a → HasQ N f b → a = b) ∧
    (∀ (N : ℕ) (f g : ℍ → ℂ) (a : ℕ → ℂ), HasQ N f a → HasQ N g a → f = g) := by sorry
