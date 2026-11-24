-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_GaussianDyadic_summable_wt
-- name    : GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic.summable_wt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:02:45.102151+00:00
-- url     : https://prove2.me/theorems/1c0261b4-4342-446c-93f0-9fbd6bf7039e
-- title:
--   Gaussian Dyadic: summable wt
-- statement:
--   The Gaussian Dyadic construction uses the summable wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianSumOfCounting.lean#L41-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianSumOfCounting.lean#L41-L72

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

theorem GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic.summable_wt {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Summable fun j : ℕ => wt c j * ((4 : ℝ) ^ n) ^ j := by sorry
