-- Prove2me | Theorems.Thm_IntMul_HvdH_fermConvRound_spec
-- name    : IntMul.HvdH.fermConvRound_spec
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T14:00:08.399985+00:00
-- url     : https://prove2.me/theorems/de36bda8-93e9-423d-bb0a-c2fc86a30c49
-- title:
--   The Fermat-ring convolution oracle has error at most √2
-- statement:
--   Let $p\ge0$, $r,P\ge1$ and $e_1,\dots,e_d\ge1$ with $2^{e_i}\mid 2r$, and put $T=r\,2^{\sum e_i}$. Assume
--   $$2\,(2^{\sum e_i})^2\,r\,(2^p)^2<2^P.$$
--   For Gaussian-integer arrays $U,V$ on the box $[0,2^{e_1})\times\cdots\times[0,2^{e_d})\times[0,r)$ with $|U(x)|,|V(x)|\le 2^p$, define $W=\mathrm{fermConvZ}(U,V)$ through four integer convolutions over the Fermat ring $\mathbb Z/(2^{2rP}+1)$. Then $\mathrm{fermConvRound}$ divides the real and imaginary parts of $W$ by $2^pT$, rounding towards zero. At every in-box index $j$ the result $Z_j$ satisfies $|Z_j|\le 2^p$ and
--   $$\Bigl|Z_j-2^p\,(\mathrm{convC}\,(2^{-p}U)\,(2^{-p}V))_j\Bigr|\le\sqrt2.$$
--   This is exactly the convolution-oracle hypothesis of the fixed-point Bluestein reduction `bluestein_fp` with $\delta=\sqrt2$. With it, the DFT of Theorem 3.1 of Harvey–van der Hoeven can be computed using integer arithmetic modulo a Fermat number.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, §3 (variant with exact convolution over a Fermat ring)

import Definitions.Def_IntMul_HvdH_FermConv

namespace IntMul.HvdH
theorem fermConvRound_spec {d : ℕ} (p P r : ℕ) (e : Fin d → ℕ) (hr : 1 ≤ r) (hP : 1 ≤ P)
    (he1 : ∀ i, 1 ≤ e i) (he : ∀ i, 2 ^ e i ∣ 2 * r)
    (hPM : 2 * (2 ^ (∑ i, e i)) ^ 2 * r * ((2 : ℤ) ^ p) ^ 2 < (2 : ℤ) ^ P) :
    ∀ U V : (Fin (d + 1) → ℕ) → ℤ × ℤ,
      (∀ x : Fin (d + 1) → ℕ, (∀ i : Fin d, x i.castSucc < 2 ^ e i) → x (Fin.last d) < r →
        ‖gC (U x)‖ ≤ 2 ^ p) →
      (∀ x : Fin (d + 1) → ℕ, (∀ i : Fin d, x i.castSucc < 2 ^ e i) → x (Fin.last d) < r →
        ‖gC (V x)‖ ≤ 2 ^ p) →
      ∀ j : Fin (d + 1) → ℕ, (∀ i : Fin d, j i.castSucc < 2 ^ e i) → j (Fin.last d) < r →
        ‖gC (fermConvRound p P r e U V j)‖ ≤ 2 ^ p ∧
        ‖gC (fermConvRound p P r e U V j) - 2 ^ p *
          convC r e (fun x => gC (U x) / 2 ^ p) (fun x => gC (V x) / 2 ^ p) j‖ ≤ Real.sqrt 2 := by sorry
end IntMul.HvdH
