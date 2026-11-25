-- Prove2me | Theorems.Thm_GlobalTheory_T_block_one_det_hermitian_gram
-- name    : GlobalTheory.T.block_one_det_hermitian_gram
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:27:22.603566+00:00
-- url     : https://prove2.me/theorems/a602715c-835a-548f-9356-0f1087611397
-- title:
--   T: block one det hermitian gram
-- statement:
--   The T construction uses the block one det hermitian gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneDetHermitianGramStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneDetHermitianGramStatement.lean#L7-L8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneDetHermitianGram
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneDetHermitianGramStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.block_one_det_hermitian_gram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F), (blockOne (algebraMap F E t) J).det = algebraMap F E t * J.det ∧ ((∀ a b, σ (J b a) = J a b) → ∀ a b, σ (blockOne (algebraMap F E t) J b a) = blockOne (algebraMap F E t) J a b) ∧ (∀ (n : ℕ) (X : Fin n → Fin M → E), gramE σ (blockOne (algebraMap F E t) J) (consTup X) = blockOne (algebraMap F E t) (gramE σ J X)) ∧ (t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (Y : Fin (n + 1) → Fin (M + 1) → E), Y 0 = Fin.cons 1 (fun _ => 0) → gramE σ (blockOne (algebraMap F E t) J) Y = blockOne (algebraMap F E t) T → ∃ X, gramE σ J X = T ∧ Y = consTup X) := by sorry
