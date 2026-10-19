-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_coarse21_stage0
-- name    : HlawkaSchatten.DiagonalCutoff21.coarse21_stage0
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-17T08:19:27.03834+00:00
-- url     : https://prove2.me/theorems/27c8aade-49b0-4c71-a5d2-315ae0125c39
-- title:
--   Cutoff 21: exact coarse LP implications, stage 0
-- statement:
--   Use the sixteen real coordinates $v_0,\ldots,v_{15}$ to encode $X_{ji}=v_{3j+i}$, $N_j=v_{9+j}$, $P_i=v_{12+i}$, and $T=v_{15}$, for $i,j\in\{0,1,2\}$. Let $L_i=\sum_{j\ne i}X_{ji}$. The hypotheses are exactly the normalized rational LP system in equation (10) of the source: singleton bounds, norm-coordinate bounds, total-coordinate bounds, nonnegative pair quantities, orientation loss, the failure inequality, and $N_0+N_1+N_2=3$. All LP parameters are exact rational numbers from the indicated profile. Then $0\le L_i\le3$ for each $i$, and $\left|\sum_{j\ne i}X_{jk}\right|\le L_i/2$ for each $k\ne i$. This is a linear implication for every assignment of the sixteen real variables; no numerical solver report is assumed.
-- source:
--   Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, v1 (2026), https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/main/paper/main.pdf . Section 3, equations (10)-(11), Table 1, and Section 8 finite certificate lemma; certificates/cutoff21/coarse.json, stage 0.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/- Adapted from the exact LP model in scripts/coarse_lp.py and the
   cutoff-21 dual witnesses. Paper Section 3, equations (10)-(11).
   v[3*j+i]=X[j,i], v[9+j]=N[j], v[12+i]=P[i], v[15]=T. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

theorem HlawkaSchatten.DiagonalCutoff21.coarse21_stage0 (v : Fin 16 → ℝ)
    (h0 : ((-1 : ℝ) * v 9) ≤ (0 : ℝ))
    (h1 : ((1 : ℝ) * v 9 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h2 : ((-1 : ℝ) * v 10) ≤ (0 : ℝ))
    (h3 : ((1 : ℝ) * v 10 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h4 : ((-1 : ℝ) * v 11) ≤ (0 : ℝ))
    (h5 : ((1 : ℝ) * v 11 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h6 : ((-1 : ℝ) * v 15) ≤ (-1 : ℝ))
    (h7 : ((1 : ℝ) * v 15) ≤ (3033 / 2500 : ℝ))
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
    (h30 : ((-1 : ℝ) * v 3 + (-1 : ℝ) * v 6 + (1 : ℝ) * v 12) ≤ (13 / 100 : ℝ))
    (h31 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 4 + (-1 : ℝ) * v 7 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h32 : ((1 : ℝ) * v 1 + (1 : ℝ) * v 4 + (1 : ℝ) * v 7 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h33 : ((-1 : ℝ) * v 13) ≤ (0 : ℝ))
    (h34 : ((-1 : ℝ) * v 9 + (-1 : ℝ) * v 11 + (1 : ℝ) * v 13) ≤ (0 : ℝ))
    (h35 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 7 + (1 : ℝ) * v 13) ≤ (13 / 100 : ℝ))
    (h36 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 5 + (-1 : ℝ) * v 8 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h37 : ((1 : ℝ) * v 2 + (1 : ℝ) * v 5 + (1 : ℝ) * v 8 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h38 : ((-1 : ℝ) * v 14) ≤ (0 : ℝ))
    (h39 : ((-1 : ℝ) * v 9 + (-1 : ℝ) * v 10 + (1 : ℝ) * v 14) ≤ (0 : ℝ))
    (h40 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 5 + (1 : ℝ) * v 14) ≤ (13 / 100 : ℝ))
    (h41 : ((-5733 / 625 : ℝ) * v 12 + (-5733 / 625 : ℝ) * v 13 + (-5733 / 625 : ℝ) * v 14 + (1 : ℝ) * v 15) ≤ (-32523 / 625 : ℝ))
    (heq : ((1 : ℝ) * v 9 + (1 : ℝ) * v 10 + (1 : ℝ) * v 11) = (3 : ℝ)) :
    (0 : ℝ) ≤ ((1 : ℝ) * v 3 + (1 : ℝ) * v 6) ∧
    (-3 : ℝ) ≤ ((-1 : ℝ) * v 3 + (-1 : ℝ) * v 6) ∧
    (0 : ℝ) ≤ ((1 / 2 : ℝ) * v 3 + (-1 : ℝ) * v 4 + (1 / 2 : ℝ) * v 6 + (-1 : ℝ) * v 7) ∧
    (0 : ℝ) ≤ ((1 / 2 : ℝ) * v 3 + (1 : ℝ) * v 4 + (1 / 2 : ℝ) * v 6 + (1 : ℝ) * v 7) ∧
    (0 : ℝ) ≤ ((1 / 2 : ℝ) * v 3 + (-1 : ℝ) * v 5 + (1 / 2 : ℝ) * v 6 + (-1 : ℝ) * v 8) ∧
    (0 : ℝ) ≤ ((1 / 2 : ℝ) * v 3 + (1 : ℝ) * v 5 + (1 / 2 : ℝ) * v 6 + (1 : ℝ) * v 8) ∧
    (0 : ℝ) ≤ ((1 : ℝ) * v 1 + (1 : ℝ) * v 7) ∧
    (-3 : ℝ) ≤ ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 7) ∧
    (0 : ℝ) ≤ ((-1 : ℝ) * v 0 + (1 / 2 : ℝ) * v 1 + (-1 : ℝ) * v 6 + (1 / 2 : ℝ) * v 7) ∧
    (0 : ℝ) ≤ ((1 : ℝ) * v 0 + (1 / 2 : ℝ) * v 1 + (1 : ℝ) * v 6 + (1 / 2 : ℝ) * v 7) ∧
    (0 : ℝ) ≤ ((1 / 2 : ℝ) * v 1 + (-1 : ℝ) * v 2 + (1 / 2 : ℝ) * v 7 + (-1 : ℝ) * v 8) ∧
    (0 : ℝ) ≤ ((1 / 2 : ℝ) * v 1 + (1 : ℝ) * v 2 + (1 / 2 : ℝ) * v 7 + (1 : ℝ) * v 8) ∧
    (0 : ℝ) ≤ ((1 : ℝ) * v 2 + (1 : ℝ) * v 5) ∧
    (-3 : ℝ) ≤ ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 5) ∧
    (0 : ℝ) ≤ ((-1 : ℝ) * v 0 + (1 / 2 : ℝ) * v 2 + (-1 : ℝ) * v 3 + (1 / 2 : ℝ) * v 5) ∧
    (0 : ℝ) ≤ ((1 : ℝ) * v 0 + (1 / 2 : ℝ) * v 2 + (1 : ℝ) * v 3 + (1 / 2 : ℝ) * v 5) ∧
    (0 : ℝ) ≤ ((-1 : ℝ) * v 1 + (1 / 2 : ℝ) * v 2 + (-1 : ℝ) * v 4 + (1 / 2 : ℝ) * v 5) ∧
    (0 : ℝ) ≤ ((1 : ℝ) * v 1 + (1 / 2 : ℝ) * v 2 + (1 : ℝ) * v 4 + (1 / 2 : ℝ) * v 5) := by sorry
