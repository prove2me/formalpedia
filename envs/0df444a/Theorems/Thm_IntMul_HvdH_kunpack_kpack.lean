-- Prove2me | Theorems.Thm_IntMul_HvdH_kunpack_kpack
-- name    : IntMul.HvdH.kunpack_kpack
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T22:50:46.799918+00:00
-- url     : https://prove2.me/theorems/d4feaeeb-bf92-4c52-8b8e-8a6b180c9552
-- title:
--   Kronecker unpacking inverts packing for balanced digits
-- statement:
--   Let $B>0$ be even and let $c=(c_0,\dots,c_{n-1})$ be integers with $2|c_i|<B$. Then reading $n$ balanced base-$B$ digits from $\sum_ic_iB^i$ recovers $c$:
--   $$\mathrm{kunpack}_B\bigl(n,\textstyle\sum_i c_iB^i\bigr)=c.$$
--   This is the unpacking step (3) of Lemma 2.5 of Harvey–van der Hoeven (see `IntMul_HvdH_KronMul`).
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Lemma 2.5 (Kronecker substitution)

import Definitions.Def_IntMul_HvdH_KronMul

namespace IntMul.HvdH
theorem kunpack_kpack (B : ℤ) (hB : 0 < B) (hBe : Even B) (c : List ℤ)
    (hc : ∀ x ∈ c, 2 * |x| < B) : kunpack B c.length (kpack B c) = c := by sorry
end IntMul.HvdH
