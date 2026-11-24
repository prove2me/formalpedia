-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceFormGram_trace_sig
-- name    : GlobalTheory.CompanionTheory.SW.TraceFormGram.trace_sig
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:11:00.569843+00:00
-- url     : https://prove2.me/theorems/7653b68f-8109-4e02-bf6c-e3b1d1ec0c48
-- title:
--   Trace Form Gram: trace sig
-- statement:
--   The Trace Form Gram construction uses the trace sig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EtaleAwayQuotientEqLocalization.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EtaleAwayQuotientEqLocalization.lean#L60-L63

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_EtaleAwayQuotientEqLocalization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TraceFormGram
open HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable [NumberField F] [NumberField E]

theorem GlobalTheory.CompanionTheory.SW.TraceFormGram.trace_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) :
    Algebra.trace F E (σ x) = Algebra.trace F E x := by sorry
