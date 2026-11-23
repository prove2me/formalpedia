-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_IsIwasawa_flatSec_of_mem
-- name    : GlobalTheory.Doubling.IsIwasawa.flatSec_of_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:22.635327+00:00
-- url     : https://prove2.me/theorems/3e7f40d4-b40d-4ac5-aba7-1d4568591630
-- title:
--   Is Iwasawa: flat Sec of mem
-- statement:
--   The Is Iwasawa construction uses the flat Sec of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L216-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L216-L217

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

theorem GlobalTheory.Doubling.IsIwasawa.flatSec_of_mem (Φ : G → ℂ) (s₀ s : ℂ) {k : G} (hk : k ∈ K) : flatSec δ K Φ s₀ s k = Φ k := by sorry
