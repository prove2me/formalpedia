-- Prove2me | Theorems.Thm_IntMul_HvdH_ct_odd
-- name    : IntMul.HvdH.ct_odd
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T21:02:26.176417+00:00
-- url     : https://prove2.me/theorems/1c84f7d3-5677-4bed-ab0e-4ae151f483b1
-- title:
--   Radix-2 Cooley–Tukey step, odd outputs
-- statement:
--   Let $R$ be a commutative ring, $m\ge0$, and $\omega\in R$ with $\omega^m=-1$. For any $u_0,u_1,\dots\in R$ and $\ell\ge0$,
--   $$\sum_{k=0}^{2m-1}\omega^{(2\ell+1)k}u_k=\sum_{k=0}^{m-1}(\omega^2)^{\ell k}\,\omega^k\,(u_k-u_{k+m}).$$
--   This is the odd half of the Cooley–Tukey butterfly (with twiddle factor $\omega^k$), as in the proof of Lemma 3.2 of Harvey–van der Hoeven.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Sections 2.4 and 3.1 (Lemma 2.3, (2.1), Lemma 3.2)

import Mathlib

namespace IntMul.HvdH
theorem ct_odd {R : Type*} [CommRing R] (m : ℕ) (ω : R) (hω : ω ^ m = -1) (u : ℕ → R) (l : ℕ) :
    ∑ k ∈ Finset.range (2 * m), ω ^ ((2 * l + 1) * k) * u k =
      ∑ k ∈ Finset.range m, (ω ^ 2) ^ (l * k) * (ω ^ k * (u k - u (k + m))) := by sorry
end IntMul.HvdH
