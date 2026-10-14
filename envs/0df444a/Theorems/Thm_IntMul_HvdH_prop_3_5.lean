-- Prove2me | Theorems.Thm_IntMul_HvdH_prop_3_5
-- name    : IntMul.HvdH.prop_3_5
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T02:23:20.789546+00:00
-- url     : https://prove2.me/theorems/c8adf0c0-732e-4814-bea7-8b22b0854cb0
-- title:
--   Fixed-point complex multidimensional convolution via twisting (Proposition 3.5)
-- statement:
--   Let $r\ge1$, $t_i=2^{e_i}$ with $2\le t_i\mid 2r$ for $i<d$, and let $p$ satisfy $2r<2^p$. Arrays on $\mathbb C^{t_1\times\cdots\times t_d\times r}$ are represented in fixed point at precision $p$ (an array $U$ of Gaussian integers stands for $2^{-p}U$, with every entry in the closed disc of radius $2^p$). Let $u*v$ denote the cyclic convolution over $\mathbb C$ in all $d+1$ axes and put $T=r\prod_it_i$. The fixed-point algorithm `convCa`, which twists by $\zeta^c$ ($\zeta=e^{\pi i/r}$) along the last axis, convolves over $\mathbb C[y]/(y^r+1)$ via synthetic FFTs (Proposition 3.4), and untwists, returns an array in the disc whose in-range entries satisfy
--   $$\Bigl\|\widetilde{\tfrac1T u*v}-2^p\,\tfrac1T\,(u*v)\Bigr\|\le 2^{\sum_ie_i}\bigl(6\textstyle\sum_ie_i+3\bigr)+23 .$$
--   This is Proposition 3.5 of Harvey–van der Hoeven (with explicit constants), the step from negacyclic to cyclic convolution in the last variable.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Proposition 3.5

import Definitions.Def_IntMul_HvdH_ConvC

namespace IntMul.HvdH
theorem prop_3_5 {d : ℕ} (p r : ℕ) (e : Fin d → ℕ) (hr : 1 ≤ r) (hrp : 2 * r < 2 ^ p)
    (he1 : ∀ i, 1 ≤ e i) (he : ∀ i, 2 ^ e i ∣ 2 * r)
    (U V : (Fin (d + 1) → ℕ) → ℤ × ℤ) (hU : InDisc p U) (hV : InDisc p V) :
    InDisc p (convCa p r e U V) ∧
      ∀ j : Fin (d + 1) → ℕ, (∀ i : Fin d, j i.castSucc < 2 ^ e i) → j (Fin.last d) < r →
        ‖gC (convCa p r e U V j) - 2 ^ p *
          convC r e (fun x => gC (U x) / 2 ^ p) (fun x => gC (V x) / 2 ^ p) j‖ ≤
          2 ^ (∑ i, e i) * (6 * (∑ i, e i) + 3) + 23  := by sorry
end IntMul.HvdH
