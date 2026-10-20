-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTAdjacentCommonInterlacing_gtSelectedPrefixWeight_finiteInterlacing_raise
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAdjacentCommonInterlacing.gtSelectedPrefixWeight_finiteInterlacing_raise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:15.843669+00:00
-- url     : https://prove2.me/theorems/135cc0fa-98df-4dee-8f54-3a53c049d725
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAdjacentCommonInterlacing.gtSelectedPrefixWeight_finiteInterlacing_raise
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MetricCodes | external Lean 4.33.1 validation; bundle SHA256 71efd718b78c759bacc3930a694e994b71f3298c205f9195221b6370cac788b3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 8000000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
set_option autoImplicit false
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAdjacentCommonInterlacing
open MetricCodes.Spherical.HigherChannel

theorem MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAdjacentCommonInterlacing.gtSelectedPrefixWeight_finiteInterlacing_raise
    {r n : ℕ} (mu : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (hn : 2 * r + 4 ≤ n)
    (hdom : Antitone mu)
    (hraiseDom : Antitone (raiseWeight mu row)) :
    FiniteInterlacing n (raiseWeight mu row)
      (gtSelectedPrefixWeight mu) := by sorry
