-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_mem_indSpace
-- name    : GlobalTheory.Doubling.mem_indSpace
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:03:59.593203+00:00
-- url     : https://prove2.me/theorems/5911e341-798f-41e7-8436-213541ec4d7f
-- title:
--   Doubling: mem ind Space
-- statement:
--   The Doubling construction uses the mem ind Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L188-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L188-L189

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

theorem GlobalTheory.Doubling.mem_indSpace [TopologicalSpace G] {Φ : G → ℂ} :
    Φ ∈ indSpace δ K χ t ↔ IndLaw δ χ t Φ ∧ Continuous Φ ∧ IsKFinite K Φ := by sorry
