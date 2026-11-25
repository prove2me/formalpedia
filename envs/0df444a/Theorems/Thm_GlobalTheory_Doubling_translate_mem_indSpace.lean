-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_translate_mem_indSpace
-- name    : GlobalTheory.Doubling.translate_mem_indSpace
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:07:31.858222+00:00
-- url     : https://prove2.me/theorems/46240b63-2188-5b76-a28e-29e4de9bbc0b
-- title:
--   Doubling: translate mem ind Space
-- statement:
--   The Doubling construction uses the translate mem ind Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L191-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L191-L193

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
variable (K)
variable {δ K χ t}

theorem GlobalTheory.Doubling.translate_mem_indSpace [TopologicalSpace G] [ContinuousMul G] {Φ : G → ℂ} (h : Φ ∈ indSpace δ K χ t) {k : G}
    (hk : k ∈ K) : (fun g => Φ (g * k)) ∈ indSpace δ K χ t := by sorry
