-- Prove2me | Theorems.Thm_GlobalTheory_IntegralMultiples_main
-- name    : GlobalTheory.IntegralMultiples.main
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:49:27.308994+00:00
-- url     : https://prove2.me/theorems/028f1966-f1ce-4b87-828f-ecbdfc4a8c79
-- title:
--   Integral Multiples: main
-- statement:
--   The Integral Multiples construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsIntMulMem.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsIntMulMem.lean#L31-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegralMultiples

theorem GlobalTheory.IntegralMultiples.main : ∀ {E : Type} [inst : Field E] [NumberField E] {r : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin r → E)),
    Submodule.span E (↑Λ : Set (Fin r → E)) = ⊤ →
      ∀ (v : Fin r → E), ∃ (k : ℤ), k ≠ (0 : ℤ) ∧ k • v ∈ Λ := by sorry
