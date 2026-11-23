-- Prove2me | Theorems.Thm_GlobalTheory_MinpolyHeightCount_finite_and_ncard_le_of_fibres_roots
-- name    : GlobalTheory.MinpolyHeightCount.finite_and_ncard_le_of_fibres_roots
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:44.490729+00:00
-- url     : https://prove2.me/theorems/8a1b72c0-b1a1-469e-87e7-23e5e14dc318
-- title:
--   Minpoly Height Count: finite and ncard le of fibres roots
-- statement:
--   The Minpoly Height Count construction uses the finite and ncard le of fibres roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FiniteAndNcardMinpolyCoeffHeightLe.lean#L37-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/FiniteAndNcardMinpolyCoeffHeightLe.lean#L37-L45

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

theorem GlobalTheory.MinpolyHeightCount.finite_and_ncard_le_of_fibres_roots {L β : Type*} [Field L] {S : Set L} {T : Set β}
    {f : L → β} (hT : T.Finite) (hf : Set.MapsTo f S T) (m : ℕ)
    (hfib : ∀ t ∈ T, ∃ p : L[X], p ≠ 0 ∧ p.natDegree ≤ m ∧ ∀ x ∈ S, f x = t → p.eval x = 0) :
    S.Finite ∧ S.ncard ≤ m * T.ncard := by sorry
