-- Prove2me | Theorems.Thm_GlobalTheory_dirPolyDeriv_eq_sum_coeff_taylorDir
-- name    : GlobalTheory.dirPolyDeriv_eq_sum_coeff_taylorDir
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:43:21.508619+00:00
-- url     : https://prove2.me/theorems/ff5f39f8-28f4-44de-a497-39a1a2efb10d
-- title:
--   Global Theory: dir Poly Deriv eq sum coeff taylor Dir
-- statement:
--   The Global Theory construction uses the dir Poly Deriv eq sum coeff taylor Dir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/MemAnalyticAtZeroOfEventuallyDifferentiableAt.lean#L111-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/MemAnalyticAtZeroOfEventuallyDifferentiableAt.lean#L111-L115

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
variable {σ W : Type*} [Fintype σ] [NormedAddCommGroup W] [NormedSpace ℂ W]
variable (u : σ → W) {f g : W → ℂ}

theorem GlobalTheory.dirPolyDeriv_eq_sum_coeff_taylorDir (P : MvPolynomial σ ℂ) (f : W → ℂ) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u f 0 = ∑ m ∈ P.support,
      P.coeff m * ((∏ i, (m i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff m (taylorDir u f) := by sorry
