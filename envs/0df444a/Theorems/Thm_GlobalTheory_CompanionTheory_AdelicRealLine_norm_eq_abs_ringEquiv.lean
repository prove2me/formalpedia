-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_AdelicRealLine_norm_eq_abs_ringEquiv
-- name    : GlobalTheory.CompanionTheory.AdelicRealLine.norm_eq_abs_ringEquiv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:16:09.373871+00:00
-- url     : https://prove2.me/theorems/af2a965e-f356-4dd1-88e8-19faf05e4a89
-- title:
--   Adelic Real Line: norm eq abs ring Equiv
-- statement:
--   The Adelic Real Line construction uses the norm eq abs ring Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TotallyRealContinuousEmbeddingInfiniteAdeles.lean#L8-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TotallyRealContinuousEmbeddingInfiniteAdeles.lean#L8-L16

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

theorem GlobalTheory.CompanionTheory.AdelicRealLine.norm_eq_abs_ringEquiv {F : Type} [Field F] {w : InfinitePlace F} (hw : w.IsReal)
    (x : w.Completion) :
    ‖x‖ = |InfinitePlace.Completion.ringEquivRealOfIsReal hw x| := by sorry
