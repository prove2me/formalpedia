-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_GaussianDyadic_radius_bound
-- name    : GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic.radius_bound
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:03:11.254442+00:00
-- url     : https://prove2.me/theorems/090c2ffd-57b5-495d-9882-b41e909bba0d
-- title:
--   Gaussian Dyadic: radius bound
-- statement:
--   The Gaussian Dyadic construction uses the radius bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianSumOfCounting.lean#L74-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianSumOfCounting.lean#L74-L103

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

theorem GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic.radius_bound (n j : ℕ) {t₀ t : ℝ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t) :
    (2 ^ j / Real.sqrt t) ^ n + (2 ^ j / Real.sqrt t) ^ (2 * n) ≤
      ((4 : ℝ) ^ n) ^ j * ((1 + (Real.sqrt t₀ ^ n)⁻¹) * (Real.sqrt t ^ n)⁻¹) := by sorry
