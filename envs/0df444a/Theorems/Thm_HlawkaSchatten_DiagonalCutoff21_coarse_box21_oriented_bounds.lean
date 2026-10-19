-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_coarse_box21_oriented_bounds
-- name    : HlawkaSchatten.DiagonalCutoff21.coarse_box21_oriented_bounds
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-17T09:12:38.733978+00:00
-- url     : https://prove2.me/theorems/d75e6bb6-675f-478e-bf95-5031a9da1a33
-- title:
--   Cutoff 21: coarse localization from oriented normalized norm data
-- statement:
--   Let $p\ge21$ be real, and let $X_0,X_1,X_2\in\mathbb R^3$. Write $N_i=\|X_i\|_p$, $T=\|X_0+X_1+X_2\|_p$ and $P_i=\|X_j+X_k\|_p$, where $\{i,j,k\}=\{0,1,2\}$. Put $A=3(1011/2500)$, $e=13/100$ and $k_0=5733/625$.
--
--   Assume $\sum_iN_i=3$, $N_i\le T$, $1\le T\le A$, and $P_i-X_{ji}-X_{ki}\le e$ for every complementary pair. Assume also $T-k_0\sum_iP_i\le3-6k_0$.
--
--   Then
--
--   $$-607/500\le X_{ii}\le-189/500,\qquad 349/500\le X_{ji}\le607/500\quad(j\ne i).$$
--
--   This is the complete two-stage coarse localization implication in Section 3 of the paper, starting from actual coordinate norms. Orientation and normalization are explicit hypotheses; a pre-established coarse box or successful numerical-check predicate is not assumed.
-- source:
--   Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, v1 (2026), https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/main/paper/main.pdf . Section 3, equations (10)-(11), parameters for Window I. The source LP and pair half-tail estimate are both proved in the submitted file.

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib.Data.Real.Basic
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff21.coarse_box21_oriented_bounds (p : ℝ) (hp : (21 : ℝ) ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (N P : Fin 3 → ℝ) (T : ℝ)
    (hNdef : ∀ i, N i = lpNorm p (X i))
    (hP0 : P 0 = lpNorm p (X 1 + X 2))
    (hP1 : P 1 = lpNorm p (X 0 + X 2))
    (hP2 : P 2 = lpNorm p (X 0 + X 1))
    (hTdef : T = lpNorm p (X 0 + X 1 + X 2))
    (hS : N 0 + N 1 + N 2 = 3) (hNT : ∀ i, N i ≤ T)
    (hT1 : 1 ≤ T) (hTcap : T ≤ (3033 / 2500 : ℝ))
    (hmain0 : P 0 - (X 1 0 + X 2 0) ≤ (13 / 100 : ℝ))
    (hmain1 : P 1 - (X 0 1 + X 2 1) ≤ (13 / 100 : ℝ))
    (hmain2 : P 2 - (X 0 2 + X 1 2) ≤ (13 / 100 : ℝ))
    (hfail : T - (5733 / 625 : ℝ) * (P 0 + P 1 + P 2) ≤ 3 - 6 * (5733 / 625 : ℝ)) :
    (∀ i, -(607 / 500 : ℝ) ≤ X i i ∧ X i i ≤ -(189 / 500 : ℝ)) ∧
    (∀ j i, j ≠ i → (349 / 500 : ℝ) ≤ X j i ∧ X j i ≤ (607 / 500 : ℝ)) := by sorry
