-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_GaussianDyadic_exists_dyadic
-- name    : GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic.exists_dyadic
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:02:52.836547+00:00
-- url     : https://prove2.me/theorems/b266a4e0-f98b-482a-8a1e-5b86a0658155
-- title:
--   Gaussian Dyadic: exists dyadic
-- statement:
--   The Gaussian Dyadic construction uses the exists dyadic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianSumOfCounting.lean#L15-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianSumOfCounting.lean#L15-L39

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

theorem GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic.exists_dyadic {c u : ℝ} (hc : 0 < c) (hu : 0 ≤ u) :
    ∃ j : ℕ, u ≤ 2 ^ j ∧ Real.exp (-(c * u ^ 2)) ≤ wt c j := by sorry
