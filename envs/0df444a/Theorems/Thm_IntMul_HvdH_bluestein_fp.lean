-- Prove2me | Theorems.Thm_IntMul_HvdH_bluestein_fp
-- name    : IntMul.HvdH.bluestein_fp
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T02:51:49.392709+00:00
-- url     : https://prove2.me/theorems/1e021fbd-526c-4e1f-917c-7a34b2fc845f
-- title:
--   Fixed-point Bluestein reduction with an arbitrary convolution oracle
-- statement:
--   Let $r$ be even, $t_i=2^{e_i}$ with $2\le t_i\mid r$ for $i<d$, and consider arrays on the box $t_1\times\cdots\times t_d\times r$ in fixed point at precision $p$. Let $M$ be any map on fixed-point arrays such that, for inputs $U,V$ in the disc of radius $2^p$ on the box, $M(U,V)$ lies in the disc on the box and
--   $$\bigl|M(U,V)_j-2^p\,\tfrac1T(u*v)_j\bigr|\le\delta\qquad(u=2^{-p}U,\ v=2^{-p}V),$$
--   where $T=r\prod_it_i$ and $*$ is the cyclic convolution `convC`. Let $A$ be a fixed-point chirp table in the disc with $|A_x-2^p a_x|\le\varepsilon_a$ on the box, where $a_x=e^{2\pi i\eta_x/(2r)}$ and $\eta_x=\sum_i\frac{r}{t_i}x_i^2+x_{d+1}^2$ (`chirpIdx`). Then Bluestein's algorithm $j\mapsto \mathrm{mulZ}\bigl(\overline{A_j},\,M(\overline A\cdot U,\,A)_j\bigr)$ stays in the disc on the box and approximates the normalised DFT:
--   $$\bigl|\widetilde{\hat u}_j-2^p\,\hat u_j\bigr|\le\delta+3\varepsilon_a+3 .$$
--   This separates Theorem 3.1 of Harvey–van der Hoeven from the way the convolution is computed. Any convolution routine (for example an exact one over a Fermat ring followed by a single rounding) and any chirp table can be plugged in.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, proof of Theorem 3.1

import Definitions.Def_IntMul_HvdH_ConvC

namespace IntMul.HvdH
theorem bluestein_fp {d : ℕ} (p r : ℕ) (e : Fin d → ℕ) (hr : 1 ≤ r) (hr2 : Even r)
    (he1 : ∀ i, 1 ≤ e i) (he : ∀ i, 2 ^ e i ∣ r)
    (M : ((Fin (d + 1) → ℕ) → ℤ × ℤ) → ((Fin (d + 1) → ℕ) → ℤ × ℤ) → (Fin (d + 1) → ℕ) → ℤ × ℤ)
    (δ : ℝ)
    (hM : ∀ U V : (Fin (d + 1) → ℕ) → ℤ × ℤ,
      (∀ x : Fin (d + 1) → ℕ, (∀ i : Fin d, x i.castSucc < 2 ^ e i) → x (Fin.last d) < r →
        ‖gC (U x)‖ ≤ 2 ^ p) →
      (∀ x : Fin (d + 1) → ℕ, (∀ i : Fin d, x i.castSucc < 2 ^ e i) → x (Fin.last d) < r →
        ‖gC (V x)‖ ≤ 2 ^ p) →
      ∀ j : Fin (d + 1) → ℕ, (∀ i : Fin d, j i.castSucc < 2 ^ e i) → j (Fin.last d) < r →
        ‖gC (M U V j)‖ ≤ 2 ^ p ∧
        ‖gC (M U V j) - 2 ^ p *
          convC r e (fun x => gC (U x) / 2 ^ p) (fun x => gC (V x) / 2 ^ p) j‖ ≤ δ)
    (A : (Fin (d + 1) → ℕ) → ℤ × ℤ) (εa : ℝ)
    (hA : ∀ x : Fin (d + 1) → ℕ, (∀ i : Fin d, x i.castSucc < 2 ^ e i) → x (Fin.last d) < r →
      ‖gC (A x)‖ ≤ 2 ^ p ∧
      ‖gC (A x) - 2 ^ p *
        Complex.exp (2 * Real.pi * Complex.I * (chirpIdx r e x : ℂ) / ((2 * r : ℕ) : ℂ))‖ ≤ εa)
    (U : (Fin (d + 1) → ℕ) → ℤ × ℤ)
    (hU : ∀ x : Fin (d + 1) → ℕ, (∀ i : Fin d, x i.castSucc < 2 ^ e i) → x (Fin.last d) < r →
      ‖gC (U x)‖ ≤ 2 ^ p) :
    ∀ j : Fin (d + 1) → ℕ, (∀ i : Fin d, j i.castSucc < 2 ^ e i) → j (Fin.last d) < r →
      ‖gC (mulZ p (conjZ (A j)) (M (fun k => mulZ p (conjZ (A k)) (U k)) A j))‖ ≤ 2 ^ p ∧
      ‖gC (mulZ p (conjZ (A j)) (M (fun k => mulZ p (conjZ (A k)) (U k)) A j)) -
        2 ^ p * dftC r e (fun x => gC (U x) / 2 ^ p) j‖ ≤ δ + 3 * εa + 3 := by sorry
end IntMul.HvdH
