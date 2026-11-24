-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatSum_sum_le_of_fibres
-- name    : GlobalTheory.CompanionTheory.SW.LatSum.sum_le_of_fibres
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:06:21.458039+00:00
-- url     : https://prove2.me/theorems/c3bb6d1f-0e4c-414d-83ef-a9137aeda689
-- title:
--   Lat Sum: sum le of fibres
-- statement:
--   The Lat Sum construction uses the sum le of fibres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EisensteinLatticeSumBound.lean#L138-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EisensteinLatticeSumBound.lean#L138-L175

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
open Classical

theorem GlobalTheory.CompanionTheory.SW.LatSum.sum_le_of_fibres {α ι : Type} [Fintype ι] (a : α → ℝ) (φ : α → ι → ℤ)
    (g : ι → ℤ → ℝ) (K : ℕ) (ha : ∀ r, 0 ≤ a r) (hg : ∀ w k, 0 ≤ g w k)
    (hgs : ∀ w, Summable (g w)) (hle : ∀ r, a r ≤ ∏ w, g w (φ r w))
    (hfib : ∀ (T : Finset α) (n : ι → ℤ), (T.filter fun r => φ r = n).card ≤ K) :
    Summable a ∧ ∑' r, a r ≤ K * ∏ w, ∑' k, g w k := by sorry
