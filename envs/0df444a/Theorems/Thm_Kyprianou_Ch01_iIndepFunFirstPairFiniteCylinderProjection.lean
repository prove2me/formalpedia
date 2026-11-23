-- Prove2me | Theorems.Thm_Kyprianou_Ch01_iIndepFunFirstPairFiniteCylinderProjection
-- name    : Kyprianou.Ch01.iIndepFunFirstPairFiniteCylinderProjection
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T19:15:35.517178+00:00
-- url     : https://prove2.me/theorems/3e0db0ac-aa4b-4cc2-9184-425dabfb061f
-- title:
--   Independent initial tagged coordinate pair and projected finite shifted tail
-- statement:
--   For a jointly independent, measurable tagged Nat⊕Nat family f, the first pair (f(inl0),f(inr0)) is independent of any finite family of successor-shifted tagged coordinates. Derive from the previously Proved disjoint finite array theorem by applying the measurable projection to the initial two coordinates and reindexing the finite tail. This result is independent of any Poisson-specific structure and suitable for reusable public import.
-- source:
--   Mathlib iIndepFun.indepFun_finset and IndepFun.comp; Kyprianou §1.3.4

import Mathlib
open MeasureTheory ProbabilityTheory Set
set_option autoImplicit false

theorem Kyprianou.Ch01.iIndepFunFirstPairFiniteCylinderProjection
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω)
    (f : (ℕ ⊕ ℕ) → Ω → ℝ)
    (hIndep : iIndepFun f Q)
    (hMeas : ∀ i : ℕ ⊕ ℕ, Measurable (f i))
    (I : Finset (ℕ ⊕ ℕ)) :
    IndepFun
      (fun w => (f (Sum.inl 0) w, f (Sum.inr 0) w))
      (fun w (i : I) => f (Sum.map Nat.succ Nat.succ i.val) w) Q := by
  sorry
