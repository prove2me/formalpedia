-- Prove2me | Theorems.Thm_IntMul_HvdH_bluestein_eq
-- name    : IntMul.HvdH.bluestein_eq
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T02:27:05.880357+00:00
-- url     : https://prove2.me/theorems/5aa9c38a-072d-4b8a-b8aa-647b0899bd74
-- title:
--   Multidimensional Bluestein identity
-- statement:
--   Let $r$ be even, $t_i=2^{e_i}$ with $2\le t_i\mid r$ for $i<d$, and put $T=r\prod_it_i$. For an index $j=(j_1,\dots,j_d,c)$ put $\chi(j)=\sum_i\frac{r}{t_i}j_i^2+c^2$ and $a(j)=e^{2\pi i\chi(j)/(2r)}$. Then the normalised DFT $\hat u(j)=\frac1T\sum_k e^{-2\pi i(\sum_i j_ik_i/t_i+j_{d+1}k_{d+1}/r)}u(k)$ satisfies, at every in-range index,
--   $$\hat u(j)=\overline{a(j)}\cdot\tfrac1T\bigl((\bar a\,u)*a\bigr)(j),$$
--   where $*$ is the cyclic convolution in all axes. This is Bluestein's chirp trick in the form used in the proof of Theorem 3.1 of Harvey–van der Hoeven.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, proof of Theorem 3.1

import Definitions.Def_IntMul_HvdH_ConvC

namespace IntMul.HvdH
theorem bluestein_eq (r : ℕ) (hr : 0 < r) (hr2 : Even r) {d : ℕ} (e : Fin d → ℕ)
    (he1 : ∀ i, 1 ≤ e i) (he : ∀ i, 2 ^ e i ∣ r) (u : (Fin (d + 1) → ℕ) → ℂ)
    (j : Fin (d + 1) → ℕ) (hj : ∀ i : Fin d, j i.castSucc < 2 ^ e i) (hc : j (Fin.last d) < r) :
    dftC r e u j =
      (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (chirpIdx r e j : ℂ) / ((2 * r : ℕ) : ℂ))) *
        convC r e (fun k => (starRingEnd ℂ)
            (Complex.exp (2 * Real.pi * Complex.I * (chirpIdx r e k : ℂ) / ((2 * r : ℕ) : ℂ))) * u k)
          (fun k => Complex.exp (2 * Real.pi * Complex.I * (chirpIdx r e k : ℂ) / ((2 * r : ℕ) : ℂ))) j  := by sorry
end IntMul.HvdH
