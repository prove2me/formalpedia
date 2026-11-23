-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceFormGram_sig_sig
-- name    : GlobalTheory.CompanionTheory.SW.TraceFormGram.sig_sig
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:51:20.859227+00:00
-- url     : https://prove2.me/theorems/0172e69e-feba-46bd-87ea-2b0b4207ff6f
-- title:
--   Trace Form Gram: sig sig
-- statement:
--   The Trace Form Gram construction uses the sig sig property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EtaleAwayQuotientEqLocalization.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EtaleAwayQuotientEqLocalization.lean#L55-L58

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

theorem GlobalTheory.CompanionTheory.SW.TraceFormGram.sig_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by sorry
