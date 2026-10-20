-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowMickelssonGramIdeal_iteratedArbitraryRowAxialRaise_append
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal.iteratedArbitraryRowAxialRaise_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:56.928481+00:00
-- url     : https://prove2.me/theorems/3b2ed62a-6cee-4826-8d72-cd1b60e1b4c1
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal.iteratedArbitraryRowAxialRaise_append
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
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherYoungMixedGapBranching
open MetricCodes.Spherical.HigherChannel

theorem MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal.iteratedArbitraryRowAxialRaise_append
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (k : Fin n)
    (rows rows' : List (Fin (r + 1))) :
    iteratedArbitraryRowAxialRaise lam k (rows ++ rows') =
      (iteratedArbitraryRowAxialRaise
        (arbitraryRowPathWeight lam rows) k rows').comp
        (iteratedArbitraryRowAxialRaise lam k rows) := by sorry
