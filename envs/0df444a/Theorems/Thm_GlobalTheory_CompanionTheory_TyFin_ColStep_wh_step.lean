-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_wh_step
-- name    : GlobalTheory.CompanionTheory.TyFin.ColStep.wh_step
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:17:48.817211+00:00
-- url     : https://prove2.me/theorems/d4f8e966-6849-4061-82a3-a2ad7d22cb72
-- title:
--   Col Step: wh step
-- statement:
--   The Col Step construction uses the wh step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalWhittaker.lean#L55-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalWhittaker.lean#L55-L68

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternSetCardColumnStepStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AdditiveCharacterSumOrthogonalityStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerColumnRecursionStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalUnipotentRadicalSumZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerVanishesOfRadicalSumsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GLTransitiveNonzeroVectorsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BlockEmbeddingGLInverseStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerBlockEmbeddingConjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalWhittaker
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.ColStep

theorem GlobalTheory.CompanionTheory.TyFin.ColStep.wh_step (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ)
    (τ : FDRep ℂ (GL (Fin d) K)) (hψ : ψ₀ ≠ 1) (hτ : IsCuspidal K τ) (hj : 1 ≤ j) (hd : j < d) :
    wh (colGe d (j + 1)) (colGeE K d (j + 1)) ψ₀ τ.character =
      ((Fintype.card K : ℂ) ^ j - 1) * wh (colGe d j) (colGeE K d j) ψ₀ τ.character := by sorry
