-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_geom_sum_int_le
-- name    : GlobalTheory.CompanionTheory.Adelic.geom_sum_int_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:16:15.395901+00:00
-- url     : https://prove2.me/theorems/29e5500c-80a8-46cf-9b2d-2edc3c5df1e1
-- title:
--   Adelic: geom sum int le
-- statement:
--   The Adelic construction uses the geom sum int le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GeomSumIntLe.lean#L8-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GeomSumIntLe.lean#L8-L114

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

theorem GlobalTheory.CompanionTheory.Adelic.geom_sum_int_le (D M : ℕ) (hD : 0 < D) (hM : 1 ≤ M) (x₀ C : ℝ) :
    ∃ C' : ℝ, ∀ r : ℝ, 0 < r →
      ∑' j : ℤ, (if (j : ℝ) + Real.log r < x₀ then 0
        else ENNReal.ofReal (C * Real.exp (2 * D * ((j : ℝ) + Real.log r)))) *
          ENNReal.ofReal (Real.exp (-(2 * D * (M + 1) * (j : ℝ)))) ≤
        ENNReal.ofReal (C' * r ^ (2 * D * (M + 1))) := by sorry
