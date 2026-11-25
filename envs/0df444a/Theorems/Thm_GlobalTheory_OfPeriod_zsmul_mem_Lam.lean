-- Prove2me | Theorems.Thm_GlobalTheory_OfPeriod_zsmul_mem_Lam
-- name    : GlobalTheory.OfPeriod.zsmul_mem_Lam
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:10.616104+00:00
-- url     : https://prove2.me/theorems/96a8227d-bce4-5f42-80cf-d52daa53afe7
-- title:
--   Of Period: zsmul mem Lam
-- statement:
--   The Of Period construction uses the zsmul mem Lam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FinrankHomComplex.lean#L242-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/FinrankHomComplex.lean#L242-L267

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
variable {S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} {R : Submodule ℝ W}

theorem GlobalTheory.OfPeriod.zsmul_mem_Lam {O : Type} [CommRing O] [StarRing O] (A : AnArc O) (k : ℤ) (z : Fin A.gB → ℂ)
    (h : ∀ l : A.abelian₂, ∃ n : ℤ, k * (A.H l z).im = n) : k • z ∈ A.abelian₂ := by sorry
