-- Prove2me | Theorems.Thm_IntMul_HvdH_twist_negacyclic
-- name    : IntMul.HvdH.twist_negacyclic
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T21:11:21.067466+00:00
-- url     : https://prove2.me/theorems/593254f8-f06c-4262-af7e-a787e185dbd4
-- title:
--   Twisting by $\zeta^j$ with $\zeta^r=-1$ turns cyclic into negacyclic convolution
-- statement:
--   Let $A$ be a commutative ring, $r\ge1$, and $\zeta\in A$ with $\zeta^r=-1$. For $u,v:\mathbb Z/r\to A$ put $a_k=\zeta^{\bar k}u_k$ and $b_k=\zeta^{\bar k}v_k$. Then the negacyclic convolution of $a,b$ is the twist of the cyclic convolution of $u,v$: for every $j$,
--   $$\sum_k a_k\,b_{j-k}\,s_{k,j}=\zeta^{\bar j}\sum_k u_kv_{j-k},\qquad s_{k,j}=\begin{cases}1&\bar k\le\bar j\\-1&\bar k>\bar j.\end{cases}$$
--   This is the coefficientwise form of the ring isomorphism $S:(\mathbb C^r,*)\to\mathbb C[y]/(y^r+1)$, $x\mapsto\zeta y$, in Proposition 3.5 of Harvey–van der Hoeven.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Sections 2.3 and 3.2 (Proposition 3.5, map S)

import Mathlib

namespace IntMul.HvdH
theorem twist_negacyclic {A : Type*} [CommRing A] (r : ℕ) [NeZero r] (ζ : A) (hζ : ζ ^ r = -1)
    (u v : ZMod r → A) (j : ZMod r) :
    ∑ k, (ζ ^ k.val * u k) * (ζ ^ (j - k).val * v (j - k)) * (if k.val ≤ j.val then 1 else -1) =
      ζ ^ j.val * ∑ k, u k * v (j - k) := by sorry
end IntMul.HvdH
