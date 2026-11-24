-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatSum_sum_int
-- name    : GlobalTheory.CompanionTheory.SW.LatSum.sum_int
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:06:18.977036+00:00
-- url     : https://prove2.me/theorems/66b419be-a431-4cb6-9e87-2183476b6cb6
-- title:
--   Lat Sum: sum int
-- statement:
--   The Lat Sum construction uses the sum int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EisensteinLatticeSumBound.lean#L54-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EisensteinLatticeSumBound.lean#L54-L94

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_EisensteinLatticeSumBound
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatSum

theorem GlobalTheory.CompanionTheory.SW.LatSum.sum_int {t y : ℝ} (ht : 0 < t) (hy : t ≤ y) (m : ℕ) :
    Summable (fun k : ℤ => ((|(k : ℝ)| + y) ^ (m + 2))⁻¹) ∧
      ∑' k : ℤ, ((|(k : ℝ)| + y) ^ (m + 2))⁻¹ ≤ 2 * (1 + 1 / t) * (y * (y ^ (m + 2))⁻¹) := by sorry
