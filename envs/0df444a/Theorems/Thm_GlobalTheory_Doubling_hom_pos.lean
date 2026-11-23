-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_hom_pos
-- name    : GlobalTheory.Doubling.hom_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:59:07.63319+00:00
-- url     : https://prove2.me/theorems/9c55ae9c-5a3f-4e7b-adcf-a61fc5f45952
-- title:
--   Doubling: hom pos
-- statement:
--   The Doubling construction uses the hom pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L15-L16

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
variable {G : Type} [Group G] {P : Subgroup G} (δ : P →* ℝ≥0) (K : Subgroup G)

theorem GlobalTheory.Doubling.hom_pos {H : Type} [Group H] (δ : H →* ℝ≥0) (p : H) : 0 < δ p := by sorry
