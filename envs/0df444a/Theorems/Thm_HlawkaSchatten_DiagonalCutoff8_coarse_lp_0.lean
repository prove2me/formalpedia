-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_coarse_lp_0
-- name    : HlawkaSchatten.DiagonalCutoff8.coarse_lp_0
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T15:36:55.881168+00:00
-- url     : https://prove2.me/theorems/8667e332-9482-4696-ab0e-1d1a9a063489
-- title:
--   Hlawka pair-coordinate refinement 1 with ratio 399/500
-- statement:
--   Let $X$ be a real $3\times3$ matrix, and let $N_i,P_i,T$ satisfy the stated linear norm bounds: $\sum_iN_i=3$, $0\le N_i\le T\in[1,57/40]$, $|X_{ji}|\le N_j$, and $|\sum_jX_{ji}|\le T$. For complementary indices $i,j,k$, assume $0\le P_i\le N_j+N_k$, $(87/100)P_i\le X_{ji}+X_{ki}$, and $T-(159/50)\sum_iP_i\le3-6(159/50)$. Retain the previous refinement bounds $P_i\le X_{ji}+X_{ki}+6\rho_r^8/8$ for $r<0$, where $(\rho_0,\rho_1,\rho_2,\rho_3)=(399/500,651/1000,539/1000,519/1000)$. Then each principal pair coordinate is nonnegative and
--   $$\max\bigl(|X_{jj}+X_{kj}|,|X_{jk}+X_{kk}|\bigr)\le\frac{399}{500}(X_{ji}+X_{ki}).$$
--   This rational linear implication is step 1 of the coarse localization for cutoff 8. The formal vector lists the nine entries of $X$, the three $N_i$, the three $P_i$, and $T$, in that order.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Exact rational consequence of the normalized coordinate and pair-gap constraints.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem HlawkaSchatten.DiagonalCutoff8.coarse_lp_0 (v : Fin 16 → ℝ)
    (h0 : ((-1 : ℝ) * v 9) ≤ (0 : ℝ))
    (h1 : ((1 : ℝ) * v 9 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h2 : ((-1 : ℝ) * v 10) ≤ (0 : ℝ))
    (h3 : ((1 : ℝ) * v 10 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h4 : ((-1 : ℝ) * v 11) ≤ (0 : ℝ))
    (h5 : ((1 : ℝ) * v 11 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h6 : ((-1 : ℝ) * v 15) ≤ (-1 : ℝ))
    (h7 : ((1 : ℝ) * v 15) ≤ (57/40 : ℝ))
    (h8 : ((-1 : ℝ) * v 0 + (-1 : ℝ) * v 9) ≤ (0 : ℝ))
    (h9 : ((1 : ℝ) * v 0 + (-1 : ℝ) * v 9) ≤ (0 : ℝ))
    (h10 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 9) ≤ (0 : ℝ))
    (h11 : ((1 : ℝ) * v 1 + (-1 : ℝ) * v 9) ≤ (0 : ℝ))
    (h12 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 9) ≤ (0 : ℝ))
    (h13 : ((1 : ℝ) * v 2 + (-1 : ℝ) * v 9) ≤ (0 : ℝ))
    (h14 : ((-1 : ℝ) * v 3 + (-1 : ℝ) * v 10) ≤ (0 : ℝ))
    (h15 : ((1 : ℝ) * v 3 + (-1 : ℝ) * v 10) ≤ (0 : ℝ))
    (h16 : ((-1 : ℝ) * v 4 + (-1 : ℝ) * v 10) ≤ (0 : ℝ))
    (h17 : ((1 : ℝ) * v 4 + (-1 : ℝ) * v 10) ≤ (0 : ℝ))
    (h18 : ((-1 : ℝ) * v 5 + (-1 : ℝ) * v 10) ≤ (0 : ℝ))
    (h19 : ((1 : ℝ) * v 5 + (-1 : ℝ) * v 10) ≤ (0 : ℝ))
    (h20 : ((-1 : ℝ) * v 6 + (-1 : ℝ) * v 11) ≤ (0 : ℝ))
    (h21 : ((1 : ℝ) * v 6 + (-1 : ℝ) * v 11) ≤ (0 : ℝ))
    (h22 : ((-1 : ℝ) * v 7 + (-1 : ℝ) * v 11) ≤ (0 : ℝ))
    (h23 : ((1 : ℝ) * v 7 + (-1 : ℝ) * v 11) ≤ (0 : ℝ))
    (h24 : ((-1 : ℝ) * v 8 + (-1 : ℝ) * v 11) ≤ (0 : ℝ))
    (h25 : ((1 : ℝ) * v 8 + (-1 : ℝ) * v 11) ≤ (0 : ℝ))
    (h26 : ((-1 : ℝ) * v 0 + (-1 : ℝ) * v 3 + (-1 : ℝ) * v 6 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h27 : ((1 : ℝ) * v 0 + (1 : ℝ) * v 3 + (1 : ℝ) * v 6 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h28 : ((-1 : ℝ) * v 12) ≤ (0 : ℝ))
    (h29 : ((-1 : ℝ) * v 10 + (-1 : ℝ) * v 11 + (1 : ℝ) * v 12) ≤ (0 : ℝ))
    (h30 : ((-1 : ℝ) * v 3 + (-1 : ℝ) * v 6 + (87/100 : ℝ) * v 12) ≤ (0 : ℝ))
    (h31 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 4 + (-1 : ℝ) * v 7 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h32 : ((1 : ℝ) * v 1 + (1 : ℝ) * v 4 + (1 : ℝ) * v 7 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h33 : ((-1 : ℝ) * v 13) ≤ (0 : ℝ))
    (h34 : ((-1 : ℝ) * v 9 + (-1 : ℝ) * v 11 + (1 : ℝ) * v 13) ≤ (0 : ℝ))
    (h35 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 7 + (87/100 : ℝ) * v 13) ≤ (0 : ℝ))
    (h36 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 5 + (-1 : ℝ) * v 8 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h37 : ((1 : ℝ) * v 2 + (1 : ℝ) * v 5 + (1 : ℝ) * v 8 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h38 : ((-1 : ℝ) * v 14) ≤ (0 : ℝ))
    (h39 : ((-1 : ℝ) * v 9 + (-1 : ℝ) * v 10 + (1 : ℝ) * v 14) ≤ (0 : ℝ))
    (h40 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 5 + (87/100 : ℝ) * v 14) ≤ (0 : ℝ))
    (h41 : ((-159/50 : ℝ) * v 12 + (-159/50 : ℝ) * v 13 + (-159/50 : ℝ) * v 14 + (1 : ℝ) * v 15) ≤ (-402/25 : ℝ))
    (heq : ((1 : ℝ) * v 9 + (1 : ℝ) * v 10 + (1 : ℝ) * v 11) = (3 : ℝ)) :
    (0 : ℝ) ≤ ((1 : ℝ) * v 3 + (1 : ℝ) * v 6) ∧
    (0 : ℝ) ≤ ((399/500 : ℝ) * v 3 + (-1 : ℝ) * v 4 + (399/500 : ℝ) * v 6 + (-1 : ℝ) * v 7) ∧
    (0 : ℝ) ≤ ((399/500 : ℝ) * v 3 + (1 : ℝ) * v 4 + (399/500 : ℝ) * v 6 + (1 : ℝ) * v 7) ∧
    (0 : ℝ) ≤ ((399/500 : ℝ) * v 3 + (-1 : ℝ) * v 5 + (399/500 : ℝ) * v 6 + (-1 : ℝ) * v 8) ∧
    (0 : ℝ) ≤ ((399/500 : ℝ) * v 3 + (1 : ℝ) * v 5 + (399/500 : ℝ) * v 6 + (1 : ℝ) * v 8) ∧
    (0 : ℝ) ≤ ((1 : ℝ) * v 1 + (1 : ℝ) * v 7) ∧
    (0 : ℝ) ≤ ((-1 : ℝ) * v 0 + (399/500 : ℝ) * v 1 + (-1 : ℝ) * v 6 + (399/500 : ℝ) * v 7) ∧
    (0 : ℝ) ≤ ((1 : ℝ) * v 0 + (399/500 : ℝ) * v 1 + (1 : ℝ) * v 6 + (399/500 : ℝ) * v 7) ∧
    (0 : ℝ) ≤ ((399/500 : ℝ) * v 1 + (-1 : ℝ) * v 2 + (399/500 : ℝ) * v 7 + (-1 : ℝ) * v 8) ∧
    (0 : ℝ) ≤ ((399/500 : ℝ) * v 1 + (1 : ℝ) * v 2 + (399/500 : ℝ) * v 7 + (1 : ℝ) * v 8) ∧
    (0 : ℝ) ≤ ((1 : ℝ) * v 2 + (1 : ℝ) * v 5) ∧
    (0 : ℝ) ≤ ((-1 : ℝ) * v 0 + (399/500 : ℝ) * v 2 + (-1 : ℝ) * v 3 + (399/500 : ℝ) * v 5) ∧
    (0 : ℝ) ≤ ((1 : ℝ) * v 0 + (399/500 : ℝ) * v 2 + (1 : ℝ) * v 3 + (399/500 : ℝ) * v 5) ∧
    (0 : ℝ) ≤ ((-1 : ℝ) * v 1 + (399/500 : ℝ) * v 2 + (-1 : ℝ) * v 4 + (399/500 : ℝ) * v 5) ∧
    (0 : ℝ) ≤ ((1 : ℝ) * v 1 + (399/500 : ℝ) * v 2 + (1 : ℝ) * v 4 + (399/500 : ℝ) * v 5) := by sorry
