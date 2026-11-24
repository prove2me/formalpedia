-- Prove2me | Theorems.Thm_GlobalTheory_Wick_factorial_smul_dividedContraction
-- name    : GlobalTheory.Wick.factorial_smul_dividedContraction
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:55:16.431119+00:00
-- url     : https://prove2.me/theorems/fcc5ee0f-834d-48d7-a2f6-419c12ca9bd3
-- title:
--   Wick: factorial smul divided Contraction
-- statement:
--   The Wick construction uses the factorial smul divided Contraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/WeightAddLeOfMemSupportDividedContraction.lean#L396-L411
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/WeightAddLeOfMemSupportDividedContraction.lean#L396-L411

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.Wick
variable {R S : Type*} [CommSemiring R] [CommSemiring S] {ι κ : Type*}
variable [Fintype κ]
variable [Fintype ι]

theorem GlobalTheory.Wick.factorial_smul_dividedContraction (γ : ι → κ → R) (n : ℕ) :
    n.factorial • dividedContraction γ n = contraction γ ^ n := by sorry
