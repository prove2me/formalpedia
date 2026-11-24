-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_sum_scalAt_eq_zero
-- name    : GlobalTheory.MinorFrame.sum_scalAt_eq_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:05:41.687769+00:00
-- url     : https://prove2.me/theorems/f990b044-6f0e-4fd2-8b6f-66e5d76a2d5f
-- title:
--   Minor Frame: sum scal At eq zero
-- statement:
--   The Minor Frame construction uses the sum scal At eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralDetCharacterFockColumnSubstitutionEqZero.lean#L65-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralDetCharacterFockColumnSubstitutionEqZero.lean#L65-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralDetCharacterFockColumnSubstitutionEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MeasureTheory
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.MinorFrame
open MvPolynomial
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.MinorFrame.sum_scalAt_eq_zero {d a : ℕ} (τ₀ : ι) (N : ℕ) (hN : 0 < N) (P : Pol ι d a) {ω : ℂ}
    (hω : IsPrimitiveRoot ω (N + P.totalDegree + 1)) :
    ∑ k ∈ Finset.range (N + P.totalDegree + 1), (ω ^ k) ^ N • colSub (scalAt τ₀ (ω ^ k)) P = 0 := by sorry
