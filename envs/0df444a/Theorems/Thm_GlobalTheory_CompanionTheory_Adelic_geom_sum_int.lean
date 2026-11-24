-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_geom_sum_int
-- name    : GlobalTheory.CompanionTheory.Adelic.geom_sum_int
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:16:21.710576+00:00
-- url     : https://prove2.me/theorems/c57fa997-0ee5-43c2-9cce-124afb5db66c
-- title:
--   Adelic: geom sum int
-- statement:
--   The Adelic construction uses the geom sum int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GeomSumIntLe.lean#L116-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GeomSumIntLe.lean#L116-L122

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GeomSumIntLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Adelic

theorem GlobalTheory.CompanionTheory.Adelic.geom_sum_int :
    ∀ (D M : ℕ), 0 < D → 1 ≤ M → ∀ (x₀ C : ℝ), ∃ C' : ℝ, ∀ r : ℝ, 0 < r →
      ∑' j : ℤ, (if (j : ℝ) + Real.log r < x₀ then 0
        else ENNReal.ofReal (C * Real.exp (2 * D * ((j : ℝ) + Real.log r)))) *
          ENNReal.ofReal (Real.exp (-(2 * D * (M + 1) * (j : ℝ)))) ≤
        ENNReal.ofReal (C' * r ^ (2 * D * (M + 1))) := by sorry
