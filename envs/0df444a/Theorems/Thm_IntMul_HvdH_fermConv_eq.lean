-- Prove2me | Theorems.Thm_IntMul_HvdH_fermConv_eq
-- name    : IntMul.HvdH.fermConv_eq
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T14:01:18.382052+00:00
-- url     : https://prove2.me/theorems/1bb92a11-eae5-449e-8d48-b08a515a6e64
-- title:
--   Exact multidimensional cyclic convolution over a Fermat ring
-- statement:
--   Let $d\ge0$, $r,P\ge1$ and $e_1,\dots,e_d\ge1$ with $t_i=2^{e_i}$ dividing $2r$. Put $T=\prod_i t_i=2^{\sum e_i}$ and $F=2^{2rP}+1$. Let $x,y$ be integer arrays on the box $[0,t_1)\times\cdots\times[0,t_d)\times[0,r)$ with all entries of absolute value at most $M$, where
--   $$2\,T^2\,r\,M^2<2^P.$$
--   The algorithm `fermConv` packs each row along the last axis as an integer $\sum_c x_{k,c}\,2^{Pc}$ reduced mod $F$. It applies the synthetic transform $\hat X(m)=\sum_k \prod_i \omega_i^{m_ik_i} X(k)\bmod F$ with $\omega_i=2^{P\cdot 4r/t_i}$ (a principal $t_i$-th root of unity mod $F$). It multiplies pointwise mod $F$, applies the inverse transform, takes the balanced residue, unpacks $2r$ base-$2^P$ digits, folds digits $c$ and $c+r$, and divides by $T$. For every in-box index $j=(j',j_{d+1})$ it returns exactly the cyclic convolution
--   $$\sum_{k\in\prod_i[0,t_i)}\sum_{c<r} x_{k,c}\;y_{(j'-k)\bmod t,\;(j_{d+1}-c)\bmod r}.$$
--   This is the exact convolution step in a machine implementation of Theorem 3.1 of Harvey–van der Hoeven: the complex convolution of fixed-point Gaussian integers is computed without error, and only one rounding is needed at the end.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, §3 (variant with exact convolution over a Fermat ring)

import Definitions.Def_IntMul_HvdH_FermConv

namespace IntMul.HvdH
theorem fermConv_eq {d : ℕ} (P r : ℕ) (e : Fin d → ℕ) (hr : 1 ≤ r) (hP : 1 ≤ P)
    (he1 : ∀ i, 1 ≤ e i) (he : ∀ i, 2 ^ e i ∣ 2 * r)
    (x y : (Fin (d + 1) → ℕ) → ℤ) (M : ℤ) (hM0 : 0 ≤ M)
    (hx : ∀ z : Fin (d + 1) → ℕ, (∀ i : Fin d, z i.castSucc < 2 ^ e i) → z (Fin.last d) < r → |x z| ≤ M)
    (hy : ∀ z : Fin (d + 1) → ℕ, (∀ i : Fin d, z i.castSucc < 2 ^ e i) → z (Fin.last d) < r → |y z| ≤ M)
    (hPM : 2 * (2 ^ (∑ i, e i)) ^ 2 * r * M ^ 2 < (2 : ℤ) ^ P)
    (j : Fin (d + 1) → ℕ) (hj : ∀ i : Fin d, j i.castSucc < 2 ^ e i) (hc : j (Fin.last d) < r) :
    fermConv P r e x y j =
      ∑ k ∈ Fintype.piFinset (fun i : Fin d => Finset.range (2 ^ e i)), ∑ c ∈ Finset.range r,
        x (Fin.snoc (fun i => k i) c) *
          y (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i)
            ((j (Fin.last d) + r - c) % r)) := by sorry
end IntMul.HvdH
