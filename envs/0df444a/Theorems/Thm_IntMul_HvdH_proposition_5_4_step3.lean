-- Prove2me | Theorems.Thm_IntMul_HvdH_proposition_5_4_step3
-- name    : IntMul.HvdH.proposition_5_4_step3
-- status  : Proved
-- author  : @avi
-- created : 2026-10-09T01:44:16.830768+00:00
-- url     : https://prove2.me/theorems/b0a122c8-f203-40d8-958b-5dbe3ecb78fa
-- title:
--   HvdH Proposition 5.4, step (3) — final error estimate $\|H''-2^{2b}S\tilde w\|<\frac14$
-- statement:
--   Let $n,b,p,\gamma,T,S$ be natural numbers with
--   $$b\ge4096,\quad p=6b,\quad\gamma<8b^{2/3},\quad1\le T<n\le2^b,\quad Tb<8n,\quad S\le T,$$
--   and let $w,\tilde w$ be vectors in a finite-dimensional space $\mathbb C^\iota$ (supremum norm) with
--   $$2^p\,\|\tilde w-w\| \;<\; 2^{\gamma+8}\,T^2\log_2T .$$
--   Then, with $H'':=2^{2b}S\,w$,
--   $$\big\|H''-2^{2b}S\,\tilde w\big\|\;<\;\tfrac14 .$$
--
--   This is the numerical heart of step (3) of the proof of Proposition 5.4: the bound $\varepsilon(\tilde w)<2^{\gamma+8}T^2\log_2T$ is the error guarantee of Proposition 5.3, and the conclusion lets one recover the integer array $H''$ exactly by rounding $2^{2b}S\tilde w$. (The paper's chain: $2^{2b}S\|w-\tilde w\|\le2^{2b}T2^{-p}\varepsilon(\tilde w)<2^{2b+\gamma+8-p}T^3\log_2T<2^{-b+\gamma+11}<\frac14$, using $T<n\le2^b$, $T\log_2T\le Tb<8n\le2^{b+3}$ and $\gamma<b-13$.)
-- source:
--   D. Harvey, J. van der Hoeven, Integer multiplication in time O(n log n), Ann. of Math. 193 (2021), https://doi.org/10.4007/annals.2021.193.2.4 (preprint https://hal.science/hal-02070778v2), proof of Proposition 5.4, step (3), p. 41 (the displayed estimates leading to ‖H'' − 2^{2b} S w̃‖ < 1/4), with (5.5), (5.6), (5.9).

import Mathlib

namespace IntMul.HvdH

theorem proposition_5_4_step3 (n b p γ T S : ℕ) (hb : 4096 ≤ b) (hp : p = 6 * b)
    (hγ : (γ : ℝ) < 8 * (b : ℝ) ^ ((2 : ℝ) / 3)) (hT1 : 1 ≤ T) (hTn : T < n) (hn : n ≤ 2 ^ b)
    (hTb : T * b < 8 * n) (hS : S ≤ T) {ι : Type*} [Fintype ι] (w w' : ι → ℂ)
    (herr : (2 : ℝ) ^ p * ‖w' - w‖ < (2 : ℝ) ^ (γ + 8) * (T : ℝ) ^ 2 * Real.logb 2 T) :
    ‖((2 : ℂ) ^ (2 * b) * S) • w - ((2 : ℂ) ^ (2 * b) * S) • w'‖ < 1 / 4 := by sorry

end IntMul.HvdH
