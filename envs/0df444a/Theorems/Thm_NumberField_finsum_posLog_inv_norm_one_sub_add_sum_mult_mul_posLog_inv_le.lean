-- Prove2me | Theorems.Thm_NumberField_finsum_posLog_inv_norm_one_sub_add_sum_mult_mul_posLog_inv_le
-- name    : NumberField.finsum_posLog_inv_norm_one_sub_add_sum_mult_mul_posLog_inv_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/025c8caa-5b8f-5152-a562-c0290e602c8f
-- title:
--   Places bound: total smallness of 1-c versus size of c
-- statement:
--   Let $F$ be a number field and $c \in F$ an arbitrary element; no hypothesis is placed on $c$. Write $\log^+ t = \max(0,\log t)$ (`Real.posLog`, so that $\log^+ 0 = 0$), let $v$ range over the height-one prime ideals of the ring of integers $\mathcal{O}_F$, with $\| \cdot \|$ the norm of the $v$-adic completion `v.adicCompletion F` applied to the image of an element of $F$, and let $w$ range over the infinite places of $F$, with $m_w$ (`w.mult`) the local degree ($1$ for a real place, $2$ for a complex one) viewed as a real number. The assertion is the inequality $$\sum_{v}^{\mathrm{f}} \log^+ \|1-c\|_v^{-1} + \sum_{w \mid \infty} m_w \log^+ \big(w(1-c)\big)^{-1} \;\le\; \sum_{v}^{\mathrm{f}} \log^+ \|c\|_v + \sum_{w \mid \infty} m_w\big(\log 2 + \log^+ w(c)\big),$$ where the inverses are taken in $\mathbb{R}$ (so $0^{-1} = 0$), the sums over infinite places are finite sums over the fintype of infinite places, and the sums over $v$ are unconditional sums (`finsum`) over the height-one spectrum; their summands have finite support, except in the degenerate case $c = 1$ where the left-hand finsum vanishes termwise.
--
--   This is the standard 'small places are paid for by large ones' estimate deduced from the product formula: the logarithmic smallness of $1-c$, summed over all places of $F$ with local degrees, is controlled by the logarithmic size of $c$ plus $\log 2$ per archimedean degree. It is used in the bound [`NumberField.sum_mult_mul_log_one_add_norm_sq_add_two_mul_finsum_log_max_norm_le_of_one_sub_mul_eq_sum`](thm.html#NumberField.sum_mult_mul_log_one_add_norm_sq_add_two_mul_finsum_log_max_norm_le_of_one_sub_mul_eq_sum), where denominators of the form $|1-c|^{-1}$ must be traded for sizes of $c$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_finsum_posLog_inv_norm_one_sub_add_sum_mult_mul_posLog_inv_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.finsum_posLog_inv_norm_one_sub_add_sum_mult_mul_posLog_inv_le
    (F : Type) [Field F] [NumberField F] (c : F) :
    (∑ᶠ v : HeightOneSpectrum (𝓞 F), Real.posLog ‖algebraMap F (v.adicCompletion F) (1 - c)‖⁻¹) +
        ∑ w : InfinitePlace F, (w.mult : ℝ) * Real.posLog (w (1 - c))⁻¹ ≤
      (∑ᶠ v : HeightOneSpectrum (𝓞 F), Real.posLog ‖algebraMap F (v.adicCompletion F) c‖) +
        ∑ w : InfinitePlace F, (w.mult : ℝ) * (Real.log 2 + Real.posLog (w c)) := by sorry
