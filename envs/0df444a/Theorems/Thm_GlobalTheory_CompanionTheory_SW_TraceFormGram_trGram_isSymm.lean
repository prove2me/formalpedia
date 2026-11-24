-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceFormGram_trGram_isSymm
-- name    : GlobalTheory.CompanionTheory.SW.TraceFormGram.trGram_isSymm
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:10:46.767191+00:00
-- url     : https://prove2.me/theorems/77c2e1c6-55f3-4f5b-a8b0-2c7b4f83cbad
-- title:
--   Trace Form Gram: tr Gram is Symm
-- statement:
--   The Trace Form Gram construction uses the tr Gram is Symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EtaleAwayQuotientEqLocalization.lean#L65-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/EtaleAwayQuotientEqLocalization.lean#L65-L73

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

theorem GlobalTheory.CompanionTheory.SW.TraceFormGram.trGram_isSymm {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {M d : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (b : Module.Basis (Fin d) F E) :
    (trGram σ J b).IsSymm := by sorry
