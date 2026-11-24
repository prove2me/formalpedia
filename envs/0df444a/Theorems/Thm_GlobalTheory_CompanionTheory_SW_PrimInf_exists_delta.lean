-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimInf_exists_delta
-- name    : GlobalTheory.CompanionTheory.SW.PrimInf.exists_delta
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:08:34.963828+00:00
-- url     : https://prove2.me/theorems/384b3f56-fe07-4635-8572-8756271e25b8
-- title:
--   Prim Inf: exists delta
-- statement:
--   The Prim Inf construction uses the exists delta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArchimedeanPrimitiveVectorCompactRescale.lean#L98-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArchimedeanPrimitiveVectorCompactRescale.lean#L98-L115

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanPrimitiveVectorCompactRescale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PrimInf
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem GlobalTheory.CompanionTheory.SW.PrimInf.exists_delta (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ δ : E, σ δ = -δ ∧ δ ≠ 0 := by sorry
