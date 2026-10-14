-- Prove2me | Theorems.Thm_IntMul_HvdH_cyclic_conv_eq_linear
-- name    : IntMul.HvdH.cyclic_conv_eq_linear
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T20:33:52.72603+00:00
-- url     : https://prove2.me/theorems/1f79b6c3-1699-4e22-a7ad-3634e6ea25ca
-- title:
--   Zero-padded cyclic convolution equals linear convolution
-- statement:
--   Let $R$ be a commutative ring and let $u,v:\mathbb N\to R$ vanish at every index $\ge n$. If $N\ge 2n-1$, then the cyclic convolution of length $N$ of the zero-padded vectors equals the ordinary (acyclic) convolution: for every $0\le k<N$,
--   $$\sum_{j\in\mathbb Z/N}u_{\bar j}\,v_{\overline{k-j}}=\sum_{i=0}^{k}u_i\,v_{k-i},$$
--   where $\bar x\in\{0,\dots,N-1\}$ is the canonical representative of $x\in\mathbb Z/N$.
--
--   This is the standard zero-padding step that lets an integer (or polynomial) product be computed by a cyclic convolution, as in §5.3 of Harvey–van der Hoeven.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Sections 2.4 and 5.3

import Mathlib

namespace IntMul.HvdH
theorem cyclic_conv_eq_linear {R : Type*} [CommRing R] {N n : ℕ} [NeZero N]
    (hN : 2 * n ≤ N + 1) (u v : ℕ → R) (hu : ∀ i, n ≤ i → u i = 0) (hv : ∀ i, n ≤ i → v i = 0)
    (k : ℕ) (hk : k < N) :
    ∑ j : ZMod N, u j.val * v ((k : ZMod N) - j).val =
      ∑ i ∈ Finset.range (k + 1), u i * v (k - i) := by sorry
end IntMul.HvdH
