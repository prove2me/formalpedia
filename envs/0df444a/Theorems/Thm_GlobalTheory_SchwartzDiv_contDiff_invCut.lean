-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzDiv_contDiff_invCut
-- name    : GlobalTheory.SchwartzDiv.contDiff_invCut
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:23.78403+00:00
-- url     : https://prove2.me/theorems/c62a944e-5d99-4d14-bc8c-39ad50e348a9
-- title:
--   Schwartz Div: cont Diff inv Cut
-- statement:
--   The Schwartz Div construction uses the cont Diff inv Cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzVanishingDecomposition.lean#L72-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzVanishingDecomposition.lean#L72-L81

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

theorem GlobalTheory.SchwartzDiv.contDiff_invCut : ContDiff ℝ ∞ invCut := by sorry
