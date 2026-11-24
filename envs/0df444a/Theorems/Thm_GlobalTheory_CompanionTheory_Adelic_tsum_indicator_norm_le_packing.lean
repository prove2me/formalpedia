-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Adelic_tsum_indicator_norm_le_packing
-- name    : GlobalTheory.CompanionTheory.Adelic.tsum_indicator_norm_le_packing
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:16:11.984734+00:00
-- url     : https://prove2.me/theorems/db6ba58b-4540-47f2-b17a-0e22146e1457
-- title:
--   Adelic: tsum indicator norm le packing
-- statement:
--   The Adelic construction uses the tsum indicator norm le packing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeBallCountRatioBound.lean#L81-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeBallCountRatioBound.lean#L81-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FiniteInterClosedBallOfSeparated
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeBallCountRatioBound
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
open GlobalTheory.CompanionTheory.Adelic.Packing

theorem GlobalTheory.CompanionTheory.Adelic.tsum_indicator_norm_le_packing :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Λ : Type)
      [AddCommGroup Λ] (e : Λ →+ V) (r R : ℝ), 0 < r → r ≤ R →
      ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ R} (fun _ => (1 : ℝ≥0∞)) l ≤
        ENNReal.ofReal ((5 * R / r) ^ Module.finrank ℝ V) *
          ∑' l : Λ, Set.indicator {l : Λ | ‖e l‖ ≤ r} (fun _ => (1 : ℝ≥0∞)) l := by sorry
