-- Prove2me | Theorems.Thm_IntMul_HvdH_eq_2_1
-- name    : IntMul.HvdH.eq_2_1
-- status  : Proved
-- author  : @avi
-- created : 2026-10-09T01:44:15.736981+00:00
-- url     : https://prove2.me/theorems/0b91511d-fef2-4fab-823d-6fac8540c3c6
-- title:
--   HvdH eq. (2.1) — multidimensional convolution formula
-- statement:
--   Let $R$ be a commutative $\mathbb C$-algebra, $d\ge0$, $n_1,\dots,n_d\ge1$, and for each $i$ let $\omega_i\in R^\times$ satisfy $\omega_i^{n_i}=1$ and $\sum_{k=0}^{n_i-1}(\omega_i^j)^k=0$ for every integer $j\not\equiv0\pmod{n_i}$. Write $N=n_1\cdots n_d$. For arrays $x$ indexed by $\prod_i\mathbb Z/n_i\mathbb Z$ and units $w_1,\dots,w_d$ put
--   $$(\mathcal F_{w}x)_j=\frac1N\sum_{k}\Big(\prod_{i=1}^d w_i^{-j_ik_i}\Big)x_k,$$
--   and let $(u*v)_j=\sum_k u_k v_{j-k}$ (componentwise subtraction mod $n_i$). Then for all arrays $u,v$,
--   $$\frac1N\,u*v \;=\; N\,\mathcal F_{\omega^{-1}}\big(\mathcal F_{\omega}u\cdot\mathcal F_{\omega}v\big).$$
--
--   This is the $d$-dimensional analogue of Lemma 2.3 (`IntMul.HvdH.lemma_2_3`). As there, the norm condition in the paper's definition of a principal root is omitted because it plays no role.
-- source:
--   D. Harvey, J. van der Hoeven, Integer multiplication in time O(n log n), Ann. of Math. 193 (2021), https://doi.org/10.4007/annals.2021.193.2.4 (preprint https://hal.science/hal-02070778v2), §2.4, equation (2.1), p. 13.

import Mathlib

namespace IntMul.HvdH

theorem eq_2_1 {R : Type*} [CommRing R] [Algebra ℂ R] {d : ℕ} (n : Fin d → ℕ)
    [∀ i, NeZero (n i)] (ω : Fin d → Rˣ) (hω : ∀ i, ω i ^ n i = 1)
    (hsum : ∀ i, ∀ j : ℤ, ¬ (n i : ℤ) ∣ j →
      ∑ k ∈ Finset.range (n i), ((ω i ^ j : Rˣ) : R) ^ k = 0)
    (u v : ((i : Fin d) → ZMod (n i)) → R) :
    let N : ℂ := ∏ i, (n i : ℂ)
    let F : (Fin d → Rˣ) → (((i : Fin d) → ZMod (n i)) → R) → ((i : Fin d) → ZMod (n i)) → R :=
      fun w x j => (1 / N) • ∑ k : (i : Fin d) → ZMod (n i),
        (∏ i, ((w i ^ (-(((j i).val * (k i).val : ℕ) : ℤ)) : Rˣ) : R)) * x k
    (1 / N) • (fun j => ∑ k : (i : Fin d) → ZMod (n i), u k * v (j - k)) =
      N • F (fun i => (ω i)⁻¹) (fun j => F ω u j * F ω v j) := by sorry

end IntMul.HvdH
