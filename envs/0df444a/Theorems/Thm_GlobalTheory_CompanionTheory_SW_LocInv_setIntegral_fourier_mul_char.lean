-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocInv_setIntegral_fourier_mul_char
-- name    : GlobalTheory.CompanionTheory.SW.LocInv.setIntegral_fourier_mul_char
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:05:31.790746+00:00
-- url     : https://prove2.me/theorems/12ef3e90-55dd-4fb4-a130-d31df0d319cb
-- title:
--   Loc Inv: set Integral fourier mul char
-- statement:
--   The Loc Inv construction uses the set Integral fourier mul char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalFieldSelfdualMeasureExists.lean#L78-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalFieldSelfdualMeasureExists.lean#L78-L137

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalFieldSelfdualMeasureExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LocInv
open GroundTheory.LocalField ValuativeRel MeasureTheory Topology Filter
open scoped NNReal ENNReal
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

theorem GlobalTheory.CompanionTheory.SW.LocInv.setIntegral_fourier_mul_char {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {Φ : K → ℂ} (hΦ : Continuous Φ) (hc : HasCompactSupport Φ) (z : K) (k : ℤ) :
    ∫ y in valBall K (addCharConductor ψ - k),
        (∫ x, Φ x * (ψ (x * y) : ℂ) ∂(selfDualMeasure ψ)) * (ψ (y * z) : ℂ) ∂(selfDualMeasure ψ) =
      (((selfDualMeasure ψ).real (valBall K (addCharConductor ψ - k)) : ℝ) : ℂ) *
        ∫ x in valBall K k, Φ (x - z) ∂(selfDualMeasure ψ) := by sorry
