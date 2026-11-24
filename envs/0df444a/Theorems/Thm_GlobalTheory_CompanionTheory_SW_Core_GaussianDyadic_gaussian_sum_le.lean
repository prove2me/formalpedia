-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_GaussianDyadic_gaussian_sum_le
-- name    : GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic.gaussian_sum_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:02:49.024864+00:00
-- url     : https://prove2.me/theorems/e8b4378d-55d0-44ff-8d56-7596f37b0b92
-- title:
--   Gaussian Dyadic: gaussian sum le
-- statement:
--   The Gaussian Dyadic construction uses the gaussian sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianSumOfCounting.lean#L127-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianSumOfCounting.lean#L127-L216

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianSumOfCounting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic

theorem GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic.gaussian_sum_le (n : ℕ) (c t₀ C : ℝ) (hc : 0 < c) (ht₀ : 0 < t₀) :
    ∀ (X Ω : Type) [MeasurableSpace Ω] [Countable X] (Pr : Measure Ω)
      (s : Ω → X → ℝ) (p : Ω → X → Prop), (∀ x, Measurable fun ω => s ω x) →
      (∀ x, MeasurableSet {ω | p ω x}) → (∀ ω x, 0 ≤ s ω x) →
      (∀ R : ℝ, 0 < R → ∫⁻ ω, ∑' x, Set.indicator {x | p ω x ∧ s ω x ≤ R}
          (fun _ => (1 : ℝ≥0∞)) x ∂Pr ≤ ENNReal.ofReal (C * (R ^ n + R ^ (2 * n)))) →
      ∀ t : ℝ, t₀ ≤ t → ∫⁻ ω, ∑' x, Set.indicator {x | p ω x}
          (fun x => ENNReal.ofReal (Real.exp (-(c * t * s ω x ^ 2)))) x ∂Pr ≤
        ENNReal.ofReal ((|C| * (1 + (Real.sqrt t₀ ^ n)⁻¹) *
          ∑' j : ℕ, wt c j * ((4 : ℝ) ^ n) ^ j) * (Real.sqrt t ^ n)⁻¹) := by sorry
