-- Prove2me | Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSpectralAbstractRTT_spectralStep_rtt
-- name    : MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralAbstractRTT.spectralStep_rtt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:00.396673+00:00
-- url     : https://prove2.me/theorems/a4fac353-c867-4155-baf4-b083a2a89a4a
-- title:
--   MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralAbstractRTT.spectralStep_rtt
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
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralAbstractRTT
open MetricCodes.Spherical.HigherHarmonicYoung

theorem MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralAbstractRTT.spectralStep_rtt
    {r n : ℕ}
    (A B C D E F S T : PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n)
    (x y : ℝ)
    (hAB : A * B = B * A)
    (hSB : S * B - B * S = D)
    (hTA : T * A - A * T = E)
    (hTB : T * B - B * T = F)
    (hSF : S * F = F * S)
    (hTC : T * C = C * T)
    (hTD : T * D = D * T)
    (hST : S * T = T * S)
    (hcross : (x - y) • (C * F - F * C) = E * D - F * C)
    (hCB : (x - y) • (C * B - B * C) = A * D - B * C)
    (hAF : (x - y) • (A * F - F * A) = E * B - F * A)
    (hEB : (x - y) • (E * B - B * E) = A * F - B * E) :
    (x - y) •
        ((x • C - A * S) * (y • F - B * T) -
          (y • F - B * T) * (x • C - A * S)) =
      (x • E - A * T) * (y • D - B * S) -
        (y • F - B * T) * (x • C - A * S) := by sorry
