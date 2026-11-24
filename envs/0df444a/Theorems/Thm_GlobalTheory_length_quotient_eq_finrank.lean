-- Prove2me | Theorems.Thm_GlobalTheory_length_quotient_eq_finrank
-- name    : GlobalTheory.length_quotient_eq_finrank
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:05:34.832312+00:00
-- url     : https://prove2.me/theorems/9154307c-7197-4348-b709-90885c58c51c
-- title:
--   Global Theory: length quotient eq finrank
-- statement:
--   The Global Theory construction uses the length quotient eq finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L208-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L208-L213

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem GlobalTheory.length_quotient_eq_finrank (p : Ideal R) (n : Ideal S) [p.IsMaximal] [n.LiesOver p]
    [Module.Finite (R ⧸ p) (S ⧸ n)] :
    Module.length R (S ⧸ n) = (Module.finrank (R ⧸ p) (S ⧸ n) : ℕ∞) := by sorry
