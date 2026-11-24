-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_IsRightSmooth_continuous
-- name    : GlobalTheory.Doubling.IsRightSmooth.continuous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:06.958814+00:00
-- url     : https://prove2.me/theorems/dffc2d95-0094-4cbc-8787-c9b32919585a
-- title:
--   Is Right Smooth: continuous
-- statement:
--   The Is Right Smooth construction uses the continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L255-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L255-L260

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

theorem GlobalTheory.Doubling.IsRightSmooth.continuous [TopologicalSpace G] [IsTopologicalGroup G] {Φ : G → ℂ} (h : IsRightSmooth Φ) :
    Continuous Φ := by sorry
