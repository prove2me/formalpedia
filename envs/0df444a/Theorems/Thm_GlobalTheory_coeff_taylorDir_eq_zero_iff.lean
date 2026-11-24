-- Prove2me | Theorems.Thm_GlobalTheory_coeff_taylorDir_eq_zero_iff
-- name    : GlobalTheory.coeff_taylorDir_eq_zero_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:43:42.622141+00:00
-- url     : https://prove2.me/theorems/c9298e9f-8d53-4ea6-86c4-07d6a2f05b63
-- title:
--   Global Theory: coeff taylor Dir eq zero iff
-- statement:
--   The Global Theory construction uses the coeff taylor Dir eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/MemAnalyticAtZeroOfEventuallyDifferentiableAt.lean#L240-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/MemAnalyticAtZeroOfEventuallyDifferentiableAt.lean#L240-L260

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

theorem GlobalTheory.coeff_taylorDir_eq_zero_iff (hu : Submodule.span ℂ (Set.range u) = ⊤)
    (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    (∀ m : σ →₀ ℕ, m.degree = n → MvPowerSeries.coeff m (taylorDir u f) = 0) ↔
      iteratedFDeriv ℂ n f 0 = 0 := by sorry
