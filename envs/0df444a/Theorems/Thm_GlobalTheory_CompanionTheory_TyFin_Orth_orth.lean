-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Orth_orth
-- name    : GlobalTheory.CompanionTheory.TyFin.Orth.orth
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:19:08.326313+00:00
-- url     : https://prove2.me/theorems/c69461ef-5112-4c6d-af82-92894b92c5d6
-- title:
--   Orth: orth
-- statement:
--   The Orth construction uses the orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AdditiveCharacterSumOrthogonality.lean#L51-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AdditiveCharacterSumOrthogonality.lean#L51-L54

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AdditiveCharacterSumOrthogonality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.Orth

theorem GlobalTheory.CompanionTheory.TyFin.Orth.orth : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (j : ℕ) (ψ₀ : AddChar K ℂ),
    ψ₀ ≠ 1 → ∀ x : Fin j → K,
    (∑ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹) = if x = 0 then (Fintype.card K : ℂ) ^ j else 0 := by sorry
