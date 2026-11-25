-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CompactOperators_isCompactOperator_of_scaled_isometric_intertwiner
-- name    : GlobalTheory.CompanionTheory.CompactOperators.isCompactOperator_of_scaled_isometric_intertwiner
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:00:29.501211+00:00
-- url     : https://prove2.me/theorems/d9efeaea-00d2-492d-b898-2828657d7290
-- title:
--   Compact Operators: is Compact Operator of scaled isometric intertwiner
-- statement:
--   The Compact Operators construction uses the is Compact Operator of scaled isometric intertwiner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsCompactOperatorOfScaledIsometricIntertwiner.lean#L7-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsCompactOperatorOfScaledIsometricIntertwiner.lean#L7-L25

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsCompactOperatorOfScaledIsometricIntertwiner
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CompactOperators

theorem GlobalTheory.CompanionTheory.CompactOperators.isCompactOperator_of_scaled_isometric_intertwiner
    {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : H →L[ℂ] H) (B : K →L[ℂ] K) (Φ : H →L[ℂ] K) (c : ℝ) (hc : 0 < c)
    (hΦ : ∀ x, ‖Φ x‖ = c * ‖x‖) (hAB : Φ ∘L A = B ∘L Φ) (hB : IsCompactOperator B) :
    IsCompactOperator A := by sorry
