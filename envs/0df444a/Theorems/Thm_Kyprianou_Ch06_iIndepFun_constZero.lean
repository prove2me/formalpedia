-- Prove2me | Theorems.Thm_Kyprianou_Ch06_iIndepFun_constZero
-- name    : Kyprianou.Ch06.iIndepFun_constZero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T21:25:19.230922+00:00
-- url     : https://prove2.me/theorems/1d02efbe-0920-453f-aa01-7c2af71cf266
-- title:
--   Finite constant-zero random-variable families are independent
-- statement:
--   For any measure of total mass one, any finite indexed family of constant-zero real random variables is mutually independent. This provides the degenerate-step component needed when translating strictly increasing time grids to non-strict monotone grids.
-- source:
--   Elementary probability consequence of finite rectangle factorisation; useful for the original Kyprianou (2006) Chapter 6 independent-increments axiom.

import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory

theorem Kyprianou.Ch06.iIndepFun_constZero
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (hprob : P Set.univ = 1) (n : Nat) :
    ProbabilityTheory.iIndepFun (fun _ : Fin n => fun _ : Ω => (0 : Real)) P := by sorry
