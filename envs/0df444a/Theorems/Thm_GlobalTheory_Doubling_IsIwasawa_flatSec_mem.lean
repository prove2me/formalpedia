-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_IsIwasawa_flatSec_mem
-- name    : GlobalTheory.Doubling.IsIwasawa.flatSec_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:50:35.091348+00:00
-- url     : https://prove2.me/theorems/40cb4621-d0b3-452f-8a7d-4b08df7117c6
-- title:
--   Is Iwasawa: flat Sec mem
-- statement:
--   The Is Iwasawa construction uses the flat Sec mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L240-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L240-L243

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
open GlobalTheory.Doubling.IsIwasawa
variable (h : IsIwasawa δ K)
include h
variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem GlobalTheory.Doubling.IsIwasawa.flatSec_mem (hP : IsClosed (P : Set G)) (hδ : Continuous δ) (hK : IsCompact (K : Set G)) {Φ : G → ℂ}
    {ρ s₀ : ℂ} (hΦ : Φ ∈ indSpace δ K χ (s₀ + ρ)) (s : ℂ) : flatSec δ K Φ s₀ s ∈ indSpace δ K χ (s + ρ) := by sorry
