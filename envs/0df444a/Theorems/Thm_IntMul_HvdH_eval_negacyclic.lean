-- Prove2me | Theorems.Thm_IntMul_HvdH_eval_negacyclic
-- name    : IntMul.HvdH.eval_negacyclic
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T21:11:08.778758+00:00
-- url     : https://prove2.me/theorems/58ebb183-6ce2-4a0f-a0bf-242b38d5ad35
-- title:
--   Multiplication in $A[y]/(y^r+1)$ is negacyclic convolution of coefficients
-- statement:
--   Let $A$ be a commutative ring, $r\ge1$, and $z\in A$ with $z^r=-1$ (for example $z=y$ in $A[y]/(y^r+1)$). For coefficient vectors $a,b:\mathbb Z/r\to A$,
--   $$\Big(\sum_j a_jz^{\bar j}\Big)\Big(\sum_j b_jz^{\bar j}\Big)=\sum_j\Big(\sum_k a_kb_{j-k}s_{k,j}\Big)z^{\bar j},$$
--   with $s_{k,j}=1$ if $\bar k\le\bar j$ and $-1$ otherwise. So multiplication in the synthetic coefficient ring $\mathbb C[y]/(y^r+1)$ of Harvey–van der Hoeven (§2.3) is negacyclic convolution on coefficient vectors, as used in Lemma 2.5 and Proposition 3.4.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Sections 2.3 and 3.2 (Proposition 3.5, map S)

import Mathlib

namespace IntMul.HvdH
theorem eval_negacyclic {A : Type*} [CommRing A] (r : ℕ) [NeZero r] (z : A) (hz : z ^ r = -1)
    (a b : ZMod r → A) :
    (∑ j, a j * z ^ j.val) * (∑ j, b j * z ^ j.val) =
      ∑ j, (∑ k, a k * b (j - k) * (if k.val ≤ j.val then 1 else -1)) * z ^ j.val := by sorry
end IntMul.HvdH
