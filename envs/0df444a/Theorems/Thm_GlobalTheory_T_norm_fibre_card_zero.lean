-- Prove2me | Theorems.Thm_GlobalTheory_T_norm_fibre_card_zero
-- name    : GlobalTheory.T.norm_fibre_card_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:29.004813+00:00
-- url     : https://prove2.me/theorems/e77a3ea7-effd-4596-aafa-c7bf6fd84e37
-- title:
--   T: norm fibre card zero
-- statement:
--   The T construction uses the norm fibre card zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormFibreCardZeroStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/NormFibreCardZeroStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardZero
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardZeroStatement
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

theorem GlobalTheory.T.norm_fibre_card_zero : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → (Nat.card {a : E // a * τ a = 0} : ℤ) = q * (1 + ε) - ε := by sorry
