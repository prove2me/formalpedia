-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_IsKFinite_translate
-- name    : GlobalTheory.Doubling.IsKFinite.translate
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:50:38.326148+00:00
-- url     : https://prove2.me/theorems/389f8b42-8e84-451a-b69f-8c0ab6e90c4e
-- title:
--   Is KFinite: translate
-- statement:
--   The Is KFinite construction uses the translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L165-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L165-L167

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open scoped NNReal
open MeasureTheory
variable {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G) (χ : P →* Circle) (t : ℂ)
variable {K}

theorem GlobalTheory.Doubling.IsKFinite.translate {Φ : G → ℂ} (h : IsKFinite K Φ) {k : G} (hk : k ∈ K) : IsKFinite K fun g => Φ (g * k) := by sorry
