-- Prove2me | Theorems.Thm_GlobalTheory_LatticeBetweenMultiples_one_add_mulVec_mem
-- name    : GlobalTheory.LatticeBetweenMultiples.one_add_mulVec_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-27T05:37:32.672309+00:00
-- url     : https://prove2.me/theorems/d609667c-a35a-5940-a1cc-d0fde43ad10f
-- title:
--   Lattice Between Multiples: one add mul Vec mem
-- statement:
--   The Lattice Between Multiples construction uses the one add mul Vec mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqMultipleOfStandardLattice.lean#L6-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqMultipleOfStandardLattice.lean#L6-L29

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

theorem GlobalTheory.LatticeBetweenMultiples.one_add_mulVec_mem {F : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {n : ℕ}
    (S : AddSubgroup (Fin n → v.adicCompletion F))
    (hGL : ∀ x : GL (Fin n) (v.adicCompletion F), (∀ i j, x.1 i j ∈ v.adicCompletionIntegers F) →
      (∀ i j, (x⁻¹).1 i j ∈ v.adicCompletionIntegers F) → ∀ w ∈ S, x.1.mulVec w ∈ S)
    (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) (hN : N * N = 0)
    (hNi : ∀ i j, N i j ∈ v.adicCompletionIntegers F) {w : Fin n → v.adicCompletion F}
    (hw : w ∈ S) : (1 + N).mulVec w ∈ S := by sorry
