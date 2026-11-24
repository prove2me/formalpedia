-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_wh_top
-- name    : GlobalTheory.CompanionTheory.TyFin.ColStep.wh_top
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:17:40.977667+00:00
-- url     : https://prove2.me/theorems/f6c5e5bc-1c75-4003-94da-77071937599a
-- title:
--   Col Step: wh top
-- statement:
--   The Col Step construction uses the wh top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalWhittaker.lean#L70-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalWhittaker.lean#L70-L96

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

theorem GlobalTheory.CompanionTheory.TyFin.ColStep.wh_top (K : Type) [Field K] [Fintype K] [DecidableEq K] (d : ℕ) (ψ₀ : AddChar K ℂ)
    (τ : FDRep ℂ (GL (Fin d) K)) :
    wh (colGe d d) (colGeE K d d) ψ₀ τ.character = (Module.finrank ℂ τ : ℂ) := by sorry
