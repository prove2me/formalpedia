-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockAlg_hE_zero_right
-- name    : GlobalTheory.CompanionTheory.SW.BlockAlg.hE_zero_right
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:03:02.170811+00:00
-- url     : https://prove2.me/theorems/48af7521-9136-4846-a10e-96ce6df98fa4
-- title:
--   Block Alg: h E zero right
-- statement:
--   The Block Alg construction uses the h E zero right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneDetHermitianGram.lean#L48-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneDetHermitianGram.lean#L48-L50

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

theorem GlobalTheory.CompanionTheory.SW.BlockAlg.hE_zero_right (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin M → E) :
    hE σ J x 0 = 0 := by sorry
