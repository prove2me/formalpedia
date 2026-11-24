-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Orth_sum_inv_addChar_mul_left
-- name    : GlobalTheory.CompanionTheory.TyFin.Orth.sum_inv_addChar_mul_left
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:19:31.561236+00:00
-- url     : https://prove2.me/theorems/a474c794-ef26-4650-af6a-266fe5e94277
-- title:
--   Orth: sum inv add Char mul left
-- statement:
--   The Orth construction uses the sum inv add Char mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AdditiveCharacterSumOrthogonality.lean#L9-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AdditiveCharacterSumOrthogonality.lean#L9-L23

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

theorem GlobalTheory.CompanionTheory.TyFin.Orth.sum_inv_addChar_mul_left (K : Type) [Field K] [Fintype K] [DecidableEq K]
    (ψ₀ : AddChar K ℂ) (hψ : ψ₀ ≠ 1) (x : K) :
    (∑ t : K, (ψ₀ (t * x))⁻¹) = if x = 0 then (Fintype.card K : ℂ) else 0 := by sorry
