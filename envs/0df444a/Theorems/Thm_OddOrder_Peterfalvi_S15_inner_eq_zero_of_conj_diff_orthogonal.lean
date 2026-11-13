-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_inner_eq_zero_of_conj_diff_orthogonal
-- name    : OddOrder.Peterfalvi.S15.inner_eq_zero_of_conj_diff_orthogonal
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:51:24.184904+00:00
-- url     : https://prove2.me/theorems/f4ed0fa6-3938-4924-9f48-c19aa01d22fc
-- title:
--   Peterfalvi (13.4): cross-$\tau$ orthogonality from orthogonal conjugation-antisymmetric differences
-- statement:
--   Let $G$ be a finite group and $A, B, C, D$ complex class functions on $G$ (`ClassFunction G ℂ`), all lying in `ZIrr G` (the $\mathbb{Z}$-span of the irreducible characters, i.e. virtual characters). Write $\langle\cdot,\cdot\rangle$ for the class-function inner product and $\bar f$ for complex conjugation (`ClassFunction.conj`). Assume
--
--   - $\langle A,A\rangle=\langle B,B\rangle=\langle C,C\rangle=\langle D,D\rangle = 1$;
--   - $\langle A,B\rangle = 0$ and $\langle C,D\rangle = 0$;
--   - $\bar A - \bar B = B - A$ and $\bar C - \bar D = D - C$;
--   - $\langle A-B,\, C-D\rangle = 0$.
--
--   Then
--   $$\langle A, C\rangle = 0 .$$
--
--   This is the "pairwise orthogonality of $\lambda^{\tau_1}$ and $\theta^{\tau_1}$" step of Peterfalvi (13.4), where the orthogonality of the differences comes from the disjoint-support input of (13.2.e).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_Tau1T.lean#L789-L859

import Definitions.Def_OddOrder_Peterfalvi_S15_NuRowPin
import Definitions.Def_OddOrder_Peterfalvi_S15_CaseACoherence
import Definitions.Def_OddOrder_Peterfalvi_S15_Tau1T

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped FiniteInduce in

theorem inner_eq_zero_of_conj_diff_orthogonal {G : Type*} [Group G] [Finite G]
    {A B C D : ClassFunction G ℂ}
    (hAZ : A ∈ ZIrr G) (hBZ : B ∈ ZIrr G) (hCZ : C ∈ ZIrr G) (hDZ : D ∈ ZIrr G)
    (hA1 : ClassFunction.inner A A = 1) (hB1 : ClassFunction.inner B B = 1)
    (hC1 : ClassFunction.inner C C = 1) (hD1 : ClassFunction.inner D D = 1)
    (hAB : ClassFunction.inner A B = 0) (hCD : ClassFunction.inner C D = 0)
    (hABconj : A.conj - B.conj = B - A) (hCDconj : C.conj - D.conj = D - C)
    (h0 : ClassFunction.inner (A - B) (C - D) = 0) :
    ClassFunction.inner A C = 0 := by sorry

end OddOrder.Peterfalvi.S15
