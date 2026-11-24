-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PrimInf_exists_basis
-- name    : GlobalTheory.CompanionTheory.SW.PrimInf.exists_basis
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:08:26.397798+00:00
-- url     : https://prove2.me/theorems/866e90b5-9d30-422b-86f0-5a20fc9dec67
-- title:
--   Prim Inf: exists basis
-- statement:
--   The Prim Inf construction uses the exists basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArchimedeanPrimitiveVectorCompactRescale.lean#L117-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArchimedeanPrimitiveVectorCompactRescale.lean#L117-L144

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

theorem GlobalTheory.CompanionTheory.SW.PrimInf.exists_basis (σ : E →ₐ[F] E) (h : IsCMExt F E σ) {δ : E} (hδ : σ δ = -δ) (h0 : δ ≠ 0) :
    ∃ b : Module.Basis (Fin 2) F E, b 0 = 1 ∧ b 1 = δ := by sorry
