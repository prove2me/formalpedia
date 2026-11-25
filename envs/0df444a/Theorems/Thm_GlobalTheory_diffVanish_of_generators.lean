-- Prove2me | Theorems.Thm_GlobalTheory_diffVanish_of_generators
-- name    : GlobalTheory.diffVanish_of_generators
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:44:47.082654+00:00
-- url     : https://prove2.me/theorems/589eb7f1-53c9-4259-a8e6-98f33f9cebed
-- title:
--   Global Theory: diff Vanish of generators
-- statement:
--   The Global Theory construction uses the diff Vanish of generators property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L167-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L167-L171

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
variable {G M : Type*} [AddCommGroup G] [AddCommGroup M]

theorem GlobalTheory.diffVanish_of_generators {S : Set G} (hS : AddSubgroup.closure S = ⊤) {n : ℕ}
    {φ : G → M} (h : ∀ g : Fin n → G, (∀ i, g i ∈ S) → multiDiff g φ = 0) :
    DiffVanish n φ := by sorry
