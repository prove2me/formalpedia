-- Prove2me | Theorems.Thm_IntMul_HvdH_thm_3_1
-- name    : IntMul.HvdH.thm_3_1
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T02:24:38.267597+00:00
-- url     : https://prove2.me/theorems/d04c7a41-2b6a-4367-84a3-9572fd021e13
-- title:
--   Fixed-point power-of-two complex multidimensional DFT (Theorem 3.1)
-- statement:
--   Let $r$ be even, $t_i=2^{e_i}$ with $2\le t_i\mid r$ for $i<d$, $T=r\prod_it_i$, and let $p$ satisfy $2r<2^p$. For a fixed-point input array $U$ on $\mathbb C^{t_1\times\cdots\times t_d\times r}$ at precision $p$ (entries in the disc of radius $2^p$, standing for $u=2^{-p}U$), the algorithm `fftCa` (Bluestein's chirp reduction to the convolution of Proposition 3.5, with fixed-point twiddles from Lemma 2.12) returns an array in the disc whose in-range entries satisfy
--   $$\bigl\|\widetilde{\hat u}(j)-2^p\,\hat u(j)\bigr\|\le 2^{\sum_ie_i}\bigl(6\textstyle\sum_ie_i+3\bigr)+41,$$
--   where $\hat u(j)=\frac1T\sum_k e^{-2\pi i(\sum_i j_ik_i/t_i+j_{d+1}k_{d+1}/r)}u(k)$ is the normalised DFT. This is Theorem 3.1 of Harvey–van der Hoeven with explicit error constants: a complex multidimensional DFT of power-of-two lengths reduces to Gaussian-integer polynomial multiplication with error $O(\log T)$ times the normalisation.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Theorem 3.1

import Definitions.Def_IntMul_HvdH_ConvC

namespace IntMul.HvdH
theorem thm_3_1 {d : ℕ} (p r : ℕ) (e : Fin d → ℕ) (hr : 1 ≤ r) (hr2 : Even r) (hrp : 2 * r < 2 ^ p)
    (he1 : ∀ i, 1 ≤ e i) (he : ∀ i, 2 ^ e i ∣ r)
    (U : (Fin (d + 1) → ℕ) → ℤ × ℤ) (hU : InDisc p U) :
    InDisc p (fftCa p r e U) ∧
      ∀ j : Fin (d + 1) → ℕ, (∀ i : Fin d, j i.castSucc < 2 ^ e i) → j (Fin.last d) < r →
        ‖gC (fftCa p r e U j) - 2 ^ p * dftC r e (fun x => gC (U x) / 2 ^ p) j‖ ≤
          2 ^ (∑ i, e i) * (6 * (∑ i, e i) + 3) + 41  := by sorry
end IntMul.HvdH
