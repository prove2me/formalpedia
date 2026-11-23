-- Prove2me | Theorems.Thm_Kyprianou_Ch01_iIndepFunFirstPairFiniteShiftedTailArrays
-- name    : Kyprianou.Ch01.iIndepFunFirstPairFiniteShiftedTailArrays
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T19:08:05.600809+00:00
-- url     : https://prove2.me/theorems/168d4076-84ff-40e1-9f82-b5717485a48c
-- title:
--   Independent first two tagged coordinates and any finite successor-shifted tail
-- statement:
--   From a jointly independent family of real-valued coordinates indexed by Nat⊕Nat, take the two initial tagged coordinates (inl 0,inr 0) and an arbitrary finite collection of coordinates shifted by Nat.succ in both branches. These index sets are disjoint. By the existing iIndepFun.indepFun_finset theorem and measurability, the two finite coordinate arrays are independent. This generic lemma is reusable for the compound-Poisson first arrival/mark pair.
-- source:
--   Pinned Mathlib iIndepFun.indepFun_finset, generic product-source independence

import Mathlib
open MeasureTheory ProbabilityTheory Set
set_option autoImplicit false

theorem Kyprianou.Ch01.iIndepFunFirstPairFiniteShiftedTailArrays
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω)
    (f : (ℕ ⊕ ℕ) → Ω → ℝ)
    (hIndep : iIndepFun f Q)
    (hMeas : ∀ i : ℕ ⊕ ℕ, Measurable (f i))
    (I S T : Finset (ℕ ⊕ ℕ))
    (hS : S = {Sum.inl 0, Sum.inr 0})
    (hT : T = I.image (Sum.map Nat.succ Nat.succ)) :
    IndepFun
      (fun w (i : S) => f i.val w)
      (fun w (i : T) => f i.val w) Q := by
  sorry
