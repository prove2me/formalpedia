-- Prove2me | Theorems.Thm_GlobalTheory_Mem_An_card_primes_mod_half
-- name    : GlobalTheory.Mem.An.card_primes_mod_half
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:51:48.856321+00:00
-- url     : https://prove2.me/theorems/086da6c1-7c3d-40a5-8f90-a86ad87bf357
-- title:
--   An: card primes mod half
-- statement:
--   The An construction uses the card primes mod half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PrimesAPIntervalOfTzRat.lean#L86-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PrimesAPIntervalOfTzRat.lean#L86-L110

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GlobalBoundRefinements
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__IsExcRat_5b5b692fee064c30
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PrimesAPIntervalOfTzRat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.HermitianLattices.GL2PrimeSums
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An

theorem GlobalTheory.Mem.An.card_primes_mod_half (n a N : ℕ) (hn : Odd n) (ha : Nat.Coprime a (2 * n)) :
    ((Icc 1 N).filter (fun p => p.Prime ∧ p ≡ a [MOD 2 * n])).card ≤
      ((Icc 1 N).filter (fun p => p.Prime ∧ p ≡ a [MOD n])).card ∧
    ((Icc 1 N).filter (fun p => p.Prime ∧ p ≡ a [MOD n])).card ≤
      ((Icc 1 N).filter (fun p => p.Prime ∧ p ≡ a [MOD 2 * n])).card + 1 := by sorry
