-- Prove2me | Theorems.Thm_IntMul_HvdH_ct_even
-- name    : IntMul.HvdH.ct_even
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T21:02:24.836584+00:00
-- url     : https://prove2.me/theorems/d439d891-7651-4175-9b36-902703577b00
-- title:
--   Radix-2 Cooley–Tukey step, even outputs
-- statement:
--   Let $R$ be a commutative ring, $m\ge0$, and $\omega\in R$ with $\omega^m=-1$. For any $u_0,u_1,\dots\in R$ and $\ell\ge0$,
--   $$\sum_{k=0}^{2m-1}\omega^{2\ell k}u_k=\sum_{k=0}^{m-1}(\omega^2)^{\ell k}\,(u_k+u_{k+m}).$$
--   Together with the odd-output identity this is the Cooley–Tukey recursion used to compute the synthetic DFT $G_t$ over $\mathbb C[y]/(y^r+1)$ in Lemma 3.2 of Harvey–van der Hoeven (there $\omega=y^{-2r/t}$ and $\omega^{t/2}=y^{-r}=-1$).
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Sections 2.4 and 3.1 (Lemma 2.3, (2.1), Lemma 3.2)

import Mathlib

namespace IntMul.HvdH
theorem ct_even {R : Type*} [CommRing R] (m : ℕ) (ω : R) (hω : ω ^ m = -1) (u : ℕ → R) (l : ℕ) :
    ∑ k ∈ Finset.range (2 * m), ω ^ (2 * l * k) * u k =
      ∑ k ∈ Finset.range m, (ω ^ 2) ^ (l * k) * (u k + u (k + m)) := by sorry
end IntMul.HvdH
