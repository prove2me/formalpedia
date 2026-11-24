-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_BlockAlg_block_alg
-- name    : GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:51:01.744027+00:00
-- url     : https://prove2.me/theorems/3a44aff5-cd95-421f-93c7-1465c8bf31bf
-- title:
--   Block Alg: block alg
-- statement:
--   The Block Alg construction uses the block alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneDetHermitianGram.lean#L99-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneDetHermitianGram.lean#L99-L111

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

theorem GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F), (blockOne (algebraMap F E t) J).det = algebraMap F E t * J.det ∧ ((∀ a b, σ (J b a) = J a b) → ∀ a b, σ (blockOne (algebraMap F E t) J b a) = blockOne (algebraMap F E t) J a b) ∧ (∀ (n : ℕ) (X : Fin n → Fin M → E), gramE σ (blockOne (algebraMap F E t) J) (consTup X) = blockOne (algebraMap F E t) (gramE σ J X)) ∧ (t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (Y : Fin (n + 1) → Fin (M + 1) → E), Y 0 = Fin.cons 1 (fun _ => 0) → gramE σ (blockOne (algebraMap F E t) J) Y = blockOne (algebraMap F E t) T → ∃ X, gramE σ J X = T ∧ Y = consTup X) := by sorry
