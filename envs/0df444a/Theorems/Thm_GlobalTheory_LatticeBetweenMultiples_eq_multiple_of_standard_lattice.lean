-- Prove2me | Theorems.Thm_GlobalTheory_LatticeBetweenMultiples_eq_multiple_of_standard_lattice
-- name    : GlobalTheory.LatticeBetweenMultiples.eq_multiple_of_standard_lattice
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-27T05:37:47.492701+00:00
-- url     : https://prove2.me/theorems/9d13ecaf-b512-45c9-843b-af87ac2279a2
-- title:
--   Lattice Between Multiples: eq multiple of standard lattice
-- statement:
--   The Lattice Between Multiples construction uses the eq multiple of standard lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqMultipleOfStandardLattice.lean#L31-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqMultipleOfStandardLattice.lean#L31-L156

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqMultipleOfStandardLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField Matrix
open GlobalTheory GlobalTheory.LatticeBetweenMultiples

theorem GlobalTheory.LatticeBetweenMultiples.eq_multiple_of_standard_lattice : ∀ {F : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {n : ℕ}
    (S : AddSubgroup (Fin n → v.adicCompletion F)),
    (∀ o ∈ v.adicCompletionIntegers F, ∀ w ∈ S, o • w ∈ S) →
    (∃ t : v.adicCompletion F, t ≠ 0 ∧ ∀ w : Fin n → v.adicCompletion F,
      (∀ i, w i ∈ v.adicCompletionIntegers F) → t • w ∈ S) →
    (∃ t : v.adicCompletion F, t ≠ 0 ∧ ∀ w ∈ S, ∀ i, t * w i ∈ v.adicCompletionIntegers F) →
    (∀ x : GL (Fin n) (v.adicCompletion F), (∀ i j, x.1 i j ∈ v.adicCompletionIntegers F) →
      (∀ i j, (x⁻¹).1 i j ∈ v.adicCompletionIntegers F) → ∀ w ∈ S, x.1.mulVec w ∈ S) →
    ∃ t : v.adicCompletion F, t ≠ 0 ∧ ∀ w, w ∈ S ↔ ∀ i, t * w i ∈ v.adicCompletionIntegers F := by sorry
