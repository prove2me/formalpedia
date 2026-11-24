-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_IsIwasawa_norm_le
-- name    : GlobalTheory.Doubling.IsIwasawa.norm_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:17.403494+00:00
-- url     : https://prove2.me/theorems/a0572242-fe5c-4d05-abe5-aecbbdb9cbf7
-- title:
--   Is Iwasawa: norm le
-- statement:
--   The Is Iwasawa construction uses the norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L232-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L232-L236

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

theorem GlobalTheory.Doubling.IsIwasawa.norm_le {Φ : G → ℂ} (hΦ : IndLaw δ χ t Φ) {C : ℝ} (hC : ∀ k ∈ K, ‖Φ k‖ ≤ C) (g : G) :
    ‖Φ g‖ ≤ C * (iwAbs δ K g : ℝ) ^ t.re := by sorry
