-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_GaussianDyadic_gaussian_le_tsum
-- name    : GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic.gaussian_le_tsum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:02:49.981119+00:00
-- url     : https://prove2.me/theorems/a68df32f-b37e-4f98-bcfc-81b52941e6e0
-- title:
--   Gaussian Dyadic: gaussian le tsum
-- statement:
--   The Gaussian Dyadic construction uses the gaussian le tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianSumOfCounting.lean#L105-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GaussianSumOfCounting.lean#L105-L125

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

theorem GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic.gaussian_le_tsum {X : Type} (c t : ℝ) (hc : 0 < c) (ht : 0 < t) (s : X → ℝ) (p : X → Prop)
    (hs : ∀ x, 0 ≤ s x) (x : X) :
    Set.indicator {x | p x} (fun x => ENNReal.ofReal (Real.exp (-(c * t * s x ^ 2)))) x ≤
      ∑' j : ℕ, ENNReal.ofReal (wt c j) *
        Set.indicator {x | p x ∧ s x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x := by sorry
