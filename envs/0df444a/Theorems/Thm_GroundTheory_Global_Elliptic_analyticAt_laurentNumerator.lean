-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_laurentNumerator
-- name    : GroundTheory.Global.Elliptic.analyticAt_laurentNumerator
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:37:30.154806+00:00
-- url     : https://prove2.me/theorems/b0bbb4ad-c70d-4106-ac15-2cb840ac7821
-- title:
--   Elliptic: analytic At laurent Numerator
-- statement:
--   The Elliptic construction uses the analytic At laurent Numerator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Residue.lean#L122-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Residue.lean#L122-L124

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Residue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic

theorem GroundTheory.Global.Elliptic.analyticAt_laurentNumerator {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p) :
    AnalyticAt ℂ (laurentNumerator f p) p := by sorry
