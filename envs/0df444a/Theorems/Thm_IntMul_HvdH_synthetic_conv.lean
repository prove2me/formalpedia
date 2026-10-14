-- Prove2me | Theorems.Thm_IntMul_HvdH_synthetic_conv
-- name    : IntMul.HvdH.synthetic_conv
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-11T21:03:07.266817+00:00
-- url     : https://prove2.me/theorems/9dbbd034-b117-483a-9c9c-4ff1dfdab3e0
-- title:
--   Multidimensional convolution formula over a ring with principal power-of-two roots (synthetic case of (2.1))
-- statement:
--   Let $R$ be a commutative ring, $d\ge0$, and for each $i$ let $n_i=2^{e_i+1}$ and $\omega_i\in R$ with $\omega_i^{2^{e_i}}=-1$. Write $\omega_i^{x}$ for $\omega_i^{\bar x}$ when $x\in\mathbb Z/n_i$ (well defined since $\omega_i^{n_i}=1$). For $u,v:\prod_i\mathbb Z/n_i\to R$ and every index $j$,
--   $$n_1\cdots n_d\,(u*v)_j=\sum_{t}\prod_i\omega_i^{t_ij_i}\Big(\sum_k\prod_i\omega_i^{-t_ik_i}u_k\Big)\Big(\sum_k\prod_i\omega_i^{-t_ik_i}v_k\Big),$$
--   where $(u*v)_j=\sum_k u_k v_{j-k}$ is multidimensional cyclic convolution.
--
--   This is the convolution formula (2.1) of Harvey–van der Hoeven in the synthetic case $R=\mathbb C[y]/(y^r+1)$, $\omega_i=y^{2r/t_i}$. It underlies Proposition 3.4 (convolution over $R$ via synthetic FFTs). The ring may have zero divisors; only $\omega_i^{2^{e_i}}=-1$ is used.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Sections 2.4 and 3.1 (Lemma 2.3, (2.1), Lemma 3.2)

import Mathlib

namespace IntMul.HvdH
theorem synthetic_conv {R : Type*} [CommRing R] {d : ℕ} (e : Fin d → ℕ) (ω : Fin d → R) (hω : ∀ i, ω i ^ (2 ^ e i) = -1)
    (u v : ((i : Fin d) → ZMod (2 ^ (e i + 1))) → R) (j : (i : Fin d) → ZMod (2 ^ (e i + 1))) :
    (∏ i, ((2 ^ (e i + 1) : ℕ) : R)) * ∑ k, u k * v (j - k) =
      ∑ t : (i : Fin d) → ZMod (2 ^ (e i + 1)), (∏ i, ω i ^ (t i * j i).val) *
        ((∑ k, (∏ i, ω i ^ (-(t i * k i)).val) * u k) *
          (∑ k, (∏ i, ω i ^ (-(t i * k i)).val) * v k)) := by sorry
end IntMul.HvdH
