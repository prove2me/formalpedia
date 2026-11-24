-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockAlg_exists_consTup_of_gramE
-- name    : GlobalTheory.CompanionTheory.SW.BlockAlg.exists_consTup_of_gramE
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:02:46.54697+00:00
-- url     : https://prove2.me/theorems/2ddbe5c7-85c9-4916-a3a7-36733ed7334a
-- title:
--   Block Alg: exists cons Tup of gram E
-- statement:
--   The Block Alg construction uses the exists cons Tup of gram E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneDetHermitianGram.lean#L71-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneDetHermitianGram.lean#L71-L97

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

theorem GlobalTheory.CompanionTheory.SW.BlockAlg.exists_consTup_of_gramE (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {t : E}
    (ht : t ≠ 0) {n : ℕ} (T : Matrix (Fin n) (Fin n) E) (Y : Fin (n + 1) → Fin (M + 1) → E)
    (h0 : Y 0 = Fin.cons 1 (fun _ => 0)) (hY : gramE σ (blockOne t J) Y = blockOne t T) :
    ∃ X, gramE σ J X = T ∧ Y = consTup X := by sorry
