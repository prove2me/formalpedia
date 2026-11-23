-- Prove2me | Theorems.Thm_GlobalTheory_IntegralMultiples_exists_int_smul_mem
-- name    : GlobalTheory.IntegralMultiples.exists_int_smul_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:59.584904+00:00
-- url     : https://prove2.me/theorems/bd53fe7a-f762-4dab-9eb4-28d3137e781d
-- title:
--   Integral Multiples: exists int smul mem
-- statement:
--   The Integral Multiples construction uses the exists int smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsIntMulMem.lean#L10-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsIntMulMem.lean#L10-L29

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

theorem GlobalTheory.IntegralMultiples.exists_int_smul_mem {E : Type} [Field E] [NumberField E] {r : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin r → E))
    (hΛ : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (v : Fin r → E) :
    ∃ k : ℤ, k ≠ 0 ∧ k • v ∈ Λ := by sorry
