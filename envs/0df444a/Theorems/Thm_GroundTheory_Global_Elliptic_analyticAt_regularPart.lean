-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_regularPart
-- name    : GroundTheory.Global.Elliptic.analyticAt_regularPart
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:37:33.170208+00:00
-- url     : https://prove2.me/theorems/8bbae66b-d06a-4b3e-9efa-f398b19c0b55
-- title:
--   Elliptic: analytic At regular Part
-- statement:
--   The Elliptic construction uses the analytic At regular Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Residue.lean#L139-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Residue.lean#L139-L141

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

theorem GroundTheory.Global.Elliptic.analyticAt_regularPart {f : ℂ → ℂ} {p : ℂ} (hf : MeromorphicAt f p) :
    AnalyticAt ℂ (regularPart f p) p := by sorry
