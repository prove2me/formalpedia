-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_coarse26_stage1
-- name    : HlawkaSchatten.DiagonalCutoff21.coarse26_stage1
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-17T08:19:27.242253+00:00
-- url     : https://prove2.me/theorems/375d29c8-7474-4d9e-9cd7-6d1746de5891
-- title:
--   Cutoff 26: exact coarse LP implications, stage 1
-- statement:
--   Use the sixteen real coordinates $v_0,\ldots,v_{15}$ to encode $X_{ji}=v_{3j+i}$, $N_j=v_{9+j}$, $P_i=v_{12+i}$, and $T=v_{15}$, for $i,j\in\{0,1,2\}$. Let $L_i=\sum_{j\ne i}X_{ji}$. The hypotheses are exactly the normalized rational LP system in equation (10) of the source: singleton bounds, norm-coordinate bounds, total-coordinate bounds, nonnegative pair quantities, orientation loss, the failure inequality, and $N_0+N_1+N_2=3$. All LP parameters are exact rational numbers from the indicated profile. Assume also the three improved pair-tail inequalities $P_i-L_i\le10^{-5}$. Then every diagonal coordinate satisfies $-1183/1000\le X_{ii}\le-477/1000$, and every off-diagonal coordinate satisfies $3/4\le X_{ji}\le 1183/1000$ for $j\ne i$. This is the second rational LP implication yielding the coarse box in equation (11).
-- source:
--   Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, v1 (2026), https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/main/paper/main.pdf . Section 3, equations (10)-(11), Table 1, and Section 8 finite certificate lemma; certificates/cutoff26/coarse.json, stage 1.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/- Adapted from the exact LP model in scripts/coarse_lp.py and the
   cutoff-26 dual witnesses. Paper Section 3, equations (10)-(11).
   v[3*j+i]=X[j,i], v[9+j]=N[j], v[12+i]=P[i], v[15]=T. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

theorem HlawkaSchatten.DiagonalCutoff21.coarse26_stage1 (v : Fin 16 → ℝ)
    (h0 : ((-1 : ℝ) * v 9) ≤ (0 : ℝ))
    (h1 : ((1 : ℝ) * v 9 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h2 : ((-1 : ℝ) * v 10) ≤ (0 : ℝ))
    (h3 : ((1 : ℝ) * v 10 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h4 : ((-1 : ℝ) * v 11) ≤ (0 : ℝ))
    (h5 : ((1 : ℝ) * v 11 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h6 : ((-1 : ℝ) * v 15) ≤ (-1 : ℝ))
    (h7 : ((1 : ℝ) * v 15) ≤ (591 / 500 : ℝ))
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
    (h30 : ((-1 : ℝ) * v 3 + (-1 : ℝ) * v 6 + (1 : ℝ) * v 12) ≤ (1 / 10 : ℝ))
    (h31 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 4 + (-1 : ℝ) * v 7 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h32 : ((1 : ℝ) * v 1 + (1 : ℝ) * v 4 + (1 : ℝ) * v 7 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h33 : ((-1 : ℝ) * v 13) ≤ (0 : ℝ))
    (h34 : ((-1 : ℝ) * v 9 + (-1 : ℝ) * v 11 + (1 : ℝ) * v 13) ≤ (0 : ℝ))
    (h35 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 7 + (1 : ℝ) * v 13) ≤ (1 / 10 : ℝ))
    (h36 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 5 + (-1 : ℝ) * v 8 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h37 : ((1 : ℝ) * v 2 + (1 : ℝ) * v 5 + (1 : ℝ) * v 8 + (-1 : ℝ) * v 15) ≤ (0 : ℝ))
    (h38 : ((-1 : ℝ) * v 14) ≤ (0 : ℝ))
    (h39 : ((-1 : ℝ) * v 9 + (-1 : ℝ) * v 10 + (1 : ℝ) * v 14) ≤ (0 : ℝ))
    (h40 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 5 + (1 : ℝ) * v 14) ≤ (1 / 10 : ℝ))
    (h41 : ((-5759 / 500 : ℝ) * v 12 + (-5759 / 500 : ℝ) * v 13 + (-5759 / 500 : ℝ) * v 14 + (1 : ℝ) * v 15) ≤ (-16527 / 250 : ℝ))
    (h42 : ((-1 : ℝ) * v 3 + (-1 : ℝ) * v 6 + (1 : ℝ) * v 12) ≤ (1 / 100000 : ℝ))
    (h43 : ((-1 : ℝ) * v 1 + (-1 : ℝ) * v 7 + (1 : ℝ) * v 13) ≤ (1 / 100000 : ℝ))
    (h44 : ((-1 : ℝ) * v 2 + (-1 : ℝ) * v 5 + (1 : ℝ) * v 14) ≤ (1 / 100000 : ℝ))
    (heq : ((1 : ℝ) * v 9 + (1 : ℝ) * v 10 + (1 : ℝ) * v 11) = (3 : ℝ)) :
    (-1183 / 1000 : ℝ) ≤ ((1 : ℝ) * v 0) ∧
    (477 / 1000 : ℝ) ≤ ((-1 : ℝ) * v 0) ∧
    (3 / 4 : ℝ) ≤ ((1 : ℝ) * v 1) ∧
    (-1183 / 1000 : ℝ) ≤ ((-1 : ℝ) * v 1) ∧
    (3 / 4 : ℝ) ≤ ((1 : ℝ) * v 2) ∧
    (-1183 / 1000 : ℝ) ≤ ((-1 : ℝ) * v 2) ∧
    (3 / 4 : ℝ) ≤ ((1 : ℝ) * v 3) ∧
    (-1183 / 1000 : ℝ) ≤ ((-1 : ℝ) * v 3) ∧
    (-1183 / 1000 : ℝ) ≤ ((1 : ℝ) * v 4) ∧
    (477 / 1000 : ℝ) ≤ ((-1 : ℝ) * v 4) ∧
    (3 / 4 : ℝ) ≤ ((1 : ℝ) * v 5) ∧
    (-1183 / 1000 : ℝ) ≤ ((-1 : ℝ) * v 5) ∧
    (3 / 4 : ℝ) ≤ ((1 : ℝ) * v 6) ∧
    (-1183 / 1000 : ℝ) ≤ ((-1 : ℝ) * v 6) ∧
    (3 / 4 : ℝ) ≤ ((1 : ℝ) * v 7) ∧
    (-1183 / 1000 : ℝ) ≤ ((-1 : ℝ) * v 7) ∧
    (-1183 / 1000 : ℝ) ≤ ((1 : ℝ) * v 8) ∧
    (477 / 1000 : ℝ) ≤ ((-1 : ℝ) * v 8) := by sorry
