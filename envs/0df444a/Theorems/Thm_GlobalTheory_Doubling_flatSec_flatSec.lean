-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_flatSec_flatSec
-- name    : GlobalTheory.Doubling.flatSec_flatSec
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:03:58.63237+00:00
-- url     : https://prove2.me/theorems/63a54228-2614-4547-918f-4605e384b678
-- title:
--   Doubling: flat Sec flat Sec
-- statement:
--   The Doubling construction uses the flat Sec flat Sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L197-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L197-L200

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

theorem GlobalTheory.Doubling.flatSec_flatSec (Φ : G → ℂ) (s₀ s₁ s : ℂ) : flatSec δ K (flatSec δ K Φ s₀ s₁) s₁ s = flatSec δ K Φ s₀ s := by sorry
