-- Prove2me | Theorems.Thm_GlobalTheory_T_card_hermitian_matrices_mod_pow
-- name    : GlobalTheory.T.card_hermitian_matrices_mod_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:27:22.45316+00:00
-- url     : https://prove2.me/theorems/cdecc9cd-8f77-4faa-b03b-a9ed5a98b424
-- title:
--   T: card hermitian matrices mod pow
-- statement:
--   The T construction uses the card hermitian matrices mod pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardHermitianMatricesModPowStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardHermitianMatricesModPowStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardHermitianMatricesModPow
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardHermitianMatricesModPowStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.card_hermitian_matrices_mod_pow : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε → ∀ n k : ℕ, Nat.card (hermMod σ ϖ n k) = q ^ (k * n ^ 2) := by sorry
