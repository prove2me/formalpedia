-- Prove2me | Theorems.Thm_IntMul_HvdH_eval_cyclic_conv
-- name    : IntMul.HvdH.eval_cyclic_conv
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T21:11:13.137132+00:00
-- url     : https://prove2.me/theorems/4fb6dd91-6ccb-43cd-8361-e81b720e5e65
-- title:
--   Evaluation at an $r$-th root of unity turns cyclic convolution into multiplication
-- statement:
--   Let $A$ be a commutative ring, $r\ge1$, and $x\in A$ with $x^r=1$. For $u,v:\mathbb Z/r\to A$,
--   $$\Big(\sum_j u_j x^{\bar j}\Big)\Big(\sum_j v_j x^{\bar j}\Big)=\sum_j (u*v)_j\,x^{\bar j},\qquad (u*v)_j=\sum_k u_kv_{j-k}.$$
--   In other words $u\mapsto\sum_j u_jx^{\bar j}$ is a ring homomorphism from $(A^r,*)\cong A[x]/(x^r-1)$ to $A$. With $x=\zeta y$ in $\mathbb C[y]/(y^r+1)$ and $\zeta=e^{\pi i/r}$ this is the ring map $S$ of Proposition 3.5 of Harvey–van der Hoeven.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Sections 2.3 and 3.2 (Proposition 3.5, map S)

import Mathlib

namespace IntMul.HvdH
theorem eval_cyclic_conv {A : Type*} [CommRing A] (r : ℕ) [NeZero r] (x : A) (hx : x ^ r = 1)
    (u v : ZMod r → A) :
    (∑ j, u j * x ^ j.val) * (∑ j, v j * x ^ j.val) = ∑ j, (∑ k, u k * v (j - k)) * x ^ j.val := by sorry
end IntMul.HvdH
