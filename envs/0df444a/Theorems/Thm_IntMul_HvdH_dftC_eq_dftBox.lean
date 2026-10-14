-- Prove2me | Theorems.Thm_IntMul_HvdH_dftC_eq_dftBox
-- name    : IntMul.HvdH.dftC_eq_dftBox
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T02:56:36.491994+00:00
-- url     : https://prove2.me/theorems/46d43b27-c0fe-4e64-8d2c-c8145566f955
-- title:
--   The DFT of Theorem 3.1 is the box DFT
-- statement:
--   Let $t_i=2^{e_i}$ for $i<d$ and $t_{d+1}=r$. For every array $x$ on $\mathbb N^{d+1}$ and every index $j$ in the box $\prod_i[0,t_i)$, the normalised DFT `dftC` of Theorem 3.1 agrees with the box DFT `dftBox` on $t=(t_1,\dots,t_d,r)$:
--   $$\frac1{r\prod_i t_i}\sum_{k,c}e^{-2\pi i(\sum_i j_ik_i/t_i+j_{d+1}c/r)}x_{(k,c)}=\frac1{\prod_i t_i'}\sum_{K\in\prod_i[0,t_i')}\prod_i\omega_{t_i'}^{-j_iK_i}x_K,\qquad \omega_N=e^{2\pi i/N}.$$
--   This connects Theorem 3.1 and `bluestein_fp` to the oracle hypothesis of `exactConv_eq`.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778

import Definitions.Def_IntMul_HvdH_ExactConv

namespace IntMul.HvdH
theorem dftC_eq_dftBox {d : ℕ} (r : ℕ) (e : Fin d → ℕ) (x : (Fin (d + 1) → ℕ) → ℂ)
    (j : Fin (d + 1) → ℕ) (hj : ∀ i : Fin d, j i.castSucc < 2 ^ e i) (hc : j (Fin.last d) < r) :
    dftC r e x j = dftBox (Fin.snoc (fun i => 2 ^ e i) r) x j := by sorry
end IntMul.HvdH
