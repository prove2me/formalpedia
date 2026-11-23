-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_dslopeIter
-- name    : GroundTheory.Global.Elliptic.analyticAt_dslopeIter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:38:56.3067+00:00
-- url     : https://prove2.me/theorems/b2611d1c-9e4a-4518-8561-db0542670d11
-- title:
--   Elliptic: analytic At dslope Iter
-- statement:
--   The Elliptic construction uses the analytic At dslope Iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Residue.lean#L36-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/Residue.lean#L36-L43

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

theorem GroundTheory.Global.Elliptic.analyticAt_dslopeIter {p : ℂ} {g : ℂ → ℂ} (hg : AnalyticAt ℂ g p) (k : ℕ) :
    AnalyticAt ℂ (dslopeIter p k g) p := by sorry
