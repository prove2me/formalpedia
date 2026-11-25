-- Prove2me | Theorems.Thm_GlobalTheory_OfPeriod_sesq_ext
-- name    : GlobalTheory.OfPeriod.sesq_ext
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:41.446861+00:00
-- url     : https://prove2.me/theorems/9f5f8ed3-5933-4688-a135-400c3061ad02
-- title:
--   Of Period: sesq ext
-- statement:
--   The Of Period construction uses the sesq ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FinrankHomComplex.lean#L52-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FinrankHomComplex.lean#L52-L56

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FinrankHomComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OfPeriod
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open Complex
variable {W : Type} [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W]

theorem GlobalTheory.OfPeriod.sesq_ext {ι : Type} {v : ι → W} (hv : Submodule.span ℝ (Set.range v) = ⊤) {S S' : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ}
    (h : ∀ i k, (S (v i) (v k)).im = (S' (v i) (v k)).im) (x y : W) : S x y = S' x y := by sorry
