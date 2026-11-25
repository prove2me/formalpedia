-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_pow_mul_of_meromorphicShift_le
-- name    : GroundTheory.Global.Elliptic.analyticAt_pow_mul_of_meromorphicShift_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:01.705035+00:00
-- url     : https://prove2.me/theorems/72e114d2-3001-418c-b520-067b69f62ccf
-- title:
--   Elliptic: analytic At pow mul of meromorphic Shift le
-- statement:
--   The Elliptic construction uses the analytic At pow mul of meromorphic Shift le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Residue.lean#L109-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Residue.lean#L109-L117

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

theorem GroundTheory.Global.Elliptic.analyticAt_pow_mul_of_meromorphicShift_le {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p)
    {n : ℕ} (hn : meromorphicShift f p ≤ n) : AnalyticAt ℂ (fun z ↦ (z - p) ^ n * f z) p := by sorry
