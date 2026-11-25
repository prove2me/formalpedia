-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_IsRightSmooth_mem_indSpace
-- name    : GlobalTheory.Doubling.IsRightSmooth.mem_indSpace
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:09:15.334801+00:00
-- url     : https://prove2.me/theorems/d88990da-d344-5d0f-9dee-46f173e65d8c
-- title:
--   Is Right Smooth: mem ind Space
-- statement:
--   The Is Right Smooth construction uses the mem ind Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L274-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L274-L275

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

theorem GlobalTheory.Doubling.IsRightSmooth.mem_indSpace [TopologicalSpace G] [IsTopologicalGroup G] {Φ : G → ℂ} (h : IsRightSmooth Φ)
    (hK : IsCompact (K : Set G)) (hl : IndLaw δ χ t Φ) : Φ ∈ indSpace δ K χ t := by sorry
