-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzDiv_invCut_of_one_le
-- name    : GlobalTheory.SchwartzDiv.invCut_of_one_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:24.069155+00:00
-- url     : https://prove2.me/theorems/6bfd26d9-6832-4603-85c9-e5b7b0b153bf
-- title:
--   Schwartz Div: inv Cut of one le
-- statement:
--   The Schwartz Div construction uses the inv Cut of one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzVanishingDecomposition.lean#L66-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzVanishingDecomposition.lean#L66-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzVanishingDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open MeasureTheory Set Filter Topology Metric
noncomputable section
open GlobalTheory GlobalTheory.SchwartzDiv

theorem GlobalTheory.SchwartzDiv.invCut_of_one_le {t : ℝ} (ht : 1 ≤ t) : invCut t = t⁻¹ := by sorry
