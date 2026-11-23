-- Prove2me | Theorems.Thm_GlobalTheory_Doubling_iwAbs_pos
-- name    : GlobalTheory.Doubling.iwAbs_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:58:28.887494+00:00
-- url     : https://prove2.me/theorems/55f5eb3d-6f4f-4138-9c7f-e2c693c3b64b
-- title:
--   Doubling: iw Abs pos
-- statement:
--   The Doubling construction uses the iw Abs pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIwasawaOfIsCompact.lean#L24-L27

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

theorem GlobalTheory.Doubling.iwAbs_pos (g : G) : 0 < iwAbs δ K g := by sorry
