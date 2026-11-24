-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocInf_isOpenEmbedding_sq
-- name    : GlobalTheory.CompanionTheory.SW.LocInf.isOpenEmbedding_sq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:06:51.800232+00:00
-- url     : https://prove2.me/theorems/dba066e7-f121-4988-9e7d-d27453734ed0
-- title:
--   Loc Inf: is Open Embedding sq
-- statement:
--   The Loc Inf construction uses the is Open Embedding sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteAdelesLocalRingTotallyReal.lean#L32-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteAdelesLocalRingTotallyReal.lean#L32-L63

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LocInf

theorem GlobalTheory.CompanionTheory.SW.LocInf.isOpenEmbedding_sq (ι : Type) [Fintype ι] :
    IsOpenEmbedding (fun u : posU ι => ((u : (ι → ℝ)ˣ) ^ 2 : (ι → ℝ)ˣ)) := by sorry
