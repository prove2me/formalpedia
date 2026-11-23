-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdelicRealLine_exists_continuous_real_embedding
-- name    : GlobalTheory.CompanionTheory.AdelicRealLine.exists_continuous_real_embedding
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:42.14412+00:00
-- url     : https://prove2.me/theorems/602588db-69db-467a-be4e-91af160c34d0
-- title:
--   Adelic Real Line: exists continuous real embedding
-- statement:
--   The Adelic Real Line construction uses the exists continuous real embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TotallyRealContinuousEmbeddingInfiniteAdeles.lean#L18-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TotallyRealContinuousEmbeddingInfiniteAdeles.lean#L18-L35

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TotallyRealContinuousEmbeddingInfiniteAdeles
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdelicRealLine

theorem GlobalTheory.CompanionTheory.AdelicRealLine.exists_continuous_real_embedding :
    ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
      (∃ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ) ∧
        ∀ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ →
          ∀ (t : ℝ) (w : InfinitePlace F), ‖θ t w‖ = |t| := by sorry
