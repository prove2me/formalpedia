-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockAlg_gramE_consTup
-- name    : GlobalTheory.CompanionTheory.SW.BlockAlg.gramE_consTup
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:02:34.867186+00:00
-- url     : https://prove2.me/theorems/5b1ddc33-6f8c-41c6-9191-e890290dd7ad
-- title:
--   Block Alg: gram E cons Tup
-- statement:
--   The Block Alg construction uses the gram E cons Tup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneDetHermitianGram.lean#L52-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneDetHermitianGram.lean#L52-L69

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneDetHermitianGram
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BlockAlg
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem GlobalTheory.CompanionTheory.SW.BlockAlg.gramE_consTup (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : E) {n : ℕ}
    (X : Fin n → Fin M → E) :
    gramE σ (blockOne t J) (consTup X) = blockOne t (gramE σ J X) := by sorry
