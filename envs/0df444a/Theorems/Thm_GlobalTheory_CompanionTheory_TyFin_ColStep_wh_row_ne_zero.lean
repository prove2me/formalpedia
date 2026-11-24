-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_wh_row_ne_zero
-- name    : GlobalTheory.CompanionTheory.TyFin.ColStep.wh_row_ne_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:18:02.687936+00:00
-- url     : https://prove2.me/theorems/ff12176a-127b-40ff-8270-5545717c0c99
-- title:
--   Col Step: wh row ne zero
-- statement:
--   The Col Step construction uses the wh row ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalWhittaker.lean#L43-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalWhittaker.lean#L43-L53

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

theorem GlobalTheory.CompanionTheory.TyFin.ColStep.wh_row_ne_zero (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ)
    (χ : GL (Fin d) K → ℂ) (hj : 1 ≤ j) (hd : j < d) (hχ : ∀ x y, χ (x * y * x⁻¹) = χ y)
    (r : Fin j → K) (hr : r ≠ 0) :
    wh (colGe d j) (colGeR K d j r) ψ₀ χ = wh (colGe d j) (colGeE K d j) ψ₀ χ := by sorry
