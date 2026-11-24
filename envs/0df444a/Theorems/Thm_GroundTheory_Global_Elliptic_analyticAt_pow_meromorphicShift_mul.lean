-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_pow_meromorphicShift_mul
-- name    : GroundTheory.Global.Elliptic.analyticAt_pow_meromorphicShift_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:37:24.531452+00:00
-- url     : https://prove2.me/theorems/8ae12792-8845-47cb-8531-ce7dde21d093
-- title:
--   Elliptic: analytic At pow meromorphic Shift mul
-- statement:
--   The Elliptic construction uses the analytic At pow meromorphic Shift mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Residue.lean#L92-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Residue.lean#L92-L99

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

theorem GroundTheory.Global.Elliptic.analyticAt_pow_meromorphicShift_mul {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p) :
    AnalyticAt ℂ (fun z ↦ (z - p) ^ meromorphicShift f p * f z) p := by sorry
