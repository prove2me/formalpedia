-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralAbstractSelfCommute_spectralStep_same_target_commute
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralAbstractSelfCommute.spectralStep_same_target_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:00.396673+00:00
-- url     : https://prove2.me/theorems/a6f37af1-48b7-4920-b738-ae8e426cc6d5
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralAbstractSelfCommute.spectralStep_same_target_commute
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
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralAbstractSelfCommute
open MetricCodes.Spherical.HigherHarmonicYoung

theorem MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralAbstractSelfCommute.spectralStep_same_target_commute
    {r n : ℕ}
    (A B C D R : PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n)
    (x y : ℝ)
    (hAB : A * B = B * A)
    (hCD : C * D = D * C)
    (hRA : R * A - A * R = C)
    (hRB : R * B - B * R = D)
    (hRC : R * C = C * R)
    (hRD : R * D = D * R)
    (hcross : (x - y) • (C * B - B * C) = A * D - B * C) :
    (x • C - A * R) * (y • D - B * R) =
      (y • D - B * R) * (x • C - A * R) := by sorry
