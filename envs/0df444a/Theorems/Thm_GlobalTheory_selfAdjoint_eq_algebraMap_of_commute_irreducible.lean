-- Prove2me | Theorems.Thm_GlobalTheory_selfAdjoint_eq_algebraMap_of_commute_irreducible
-- name    : GlobalTheory.selfAdjoint_eq_algebraMap_of_commute_irreducible
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:20:25.605698+00:00
-- url     : https://prove2.me/theorems/b70f2c76-a7fd-4979-a5d5-eb16d1fb12d9
-- title:
--   Global Theory: self Adjoint eq algebra Map of commute irreducible
-- statement:
--   The Global Theory construction uses the self Adjoint eq algebra Map of commute irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SelfAdjointEqAlgebraMapOfCommuteIrreducible.lean#L7-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/SelfAdjointEqAlgebraMapOfCommuteIrreducible.lean#L7-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SelfAdjointEqAlgebraMapOfCommuteIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open GlobalTheory

theorem GlobalTheory.selfAdjoint_eq_algebraMap_of_commute_irreducible {G H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (π : G → (H →L[ℂ] H))
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ u ∈ S, π g u ∈ S) →
      S = ⊥ ∨ S = ⊤)
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (hc : ∀ g, Commute A (π g)) :
    ∃ r : ℝ, A = algebraMap ℝ (H →L[ℂ] H) r := by sorry
