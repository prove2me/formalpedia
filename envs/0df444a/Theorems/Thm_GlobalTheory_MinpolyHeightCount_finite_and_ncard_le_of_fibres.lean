-- Prove2me | Theorems.Thm_GlobalTheory_MinpolyHeightCount_finite_and_ncard_le_of_fibres
-- name    : GlobalTheory.MinpolyHeightCount.finite_and_ncard_le_of_fibres
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:24:58.251903+00:00
-- url     : https://prove2.me/theorems/9c33d725-d79f-4cd8-a520-5f03714332bc
-- title:
--   Minpoly Height Count: finite and ncard le of fibres
-- statement:
--   The Minpoly Height Count construction uses the finite and ncard le of fibres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FiniteAndNcardMinpolyCoeffHeightLe.lean#L7-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FiniteAndNcardMinpolyCoeffHeightLe.lean#L7-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FiniteAndNcardMinpolyCoeffHeightLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open GlobalTheory GlobalTheory.MinpolyHeightCount

theorem GlobalTheory.MinpolyHeightCount.finite_and_ncard_le_of_fibres {α β : Type*} {S : Set α} {T : Set β} {f : α → β}
    (hT : T.Finite) (hf : Set.MapsTo f S T) (m : ℕ)
    (hfib : ∀ t ∈ T, (S ∩ f ⁻¹' {t}).Finite ∧ (S ∩ f ⁻¹' {t}).ncard ≤ m) :
    S.Finite ∧ S.ncard ≤ m * T.ncard := by sorry
