-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_coarse_failure_window01
-- name    : HlawkaSchatten.DiagonalCutoff16.coarse_failure_window01
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-26T00:07:22.271691+00:00
-- url     : https://prove2.me/theorems/44088b88-02ec-44d5-9c7a-c318492ea0a5
-- title:
--   Coarse Hlawka counterexample localization for 513/32 <= p <= 257/16
-- statement:
--   Let $513/32\le p\le 257/16$ and let $K_p$ be the cyclic Hlawka constant. If some triple in $\mathbb R^3$ violates the Hlawka inequality with constant $K_p$, there exists a normalized violating triple $X=(X_0,X_1,X_2)$ with
--   $$\sum_i\|X_i\|_p=3,\qquad 1\le T:=\|X_0+X_1+X_2\|_p<62967/50000,\qquad 42773/100000p\le K_p\le p/2.$$
--   Its diagonal coordinates lie in $[-6297/5000,-1137/5000]$ and its off-diagonal coordinates lie in $[1541/2500,6297/5000]$. If $G=6-(\|X_0+X_1\|_p+\|X_0+X_2\|_p+\|X_1+X_2\|_p)$, then
--   $$(42773/100000p)G+T<3.$$
--   For every permutation $(i,j,k)$ of $(0,1,2)$,
--   $$\|X_j+X_k\|_p\le X_j(i)+X_k(i)+1/100000000.$$
--   These common bounds localize every potential counterexample in this exponent window. Separate total-norm, contraction and curvature estimates are still needed to exclude it.
-- source:
--   Cutoff-16 extension, reusable coarse localization component. Reuses attributed Apache-2.0 normalization and orientation arguments of Ezzeri Esa, bwdaugherty and Yuxuan Xu from accepted Prove2Me submission 4753aff4-c621-4df6-9535-63c865f87fd0. The scalar bounds, exact linear-programming implications and one-third pair-tail certificates for this window are checked afresh in the proof.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff16.coarse_failure_window01 (p : ℝ) (hpa : (513/32 : ℝ) ≤ p) (hpb : p ≤ (257/16 : ℝ))
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    ∃ X : Fin 3 → Fin 3 → ℝ,
      ((42773/100000 : ℝ)*p ≤ cyclicConstant p) ∧ (cyclicConstant p ≤ p/2) ∧
      (∀ j i, if j = i then -(6297/5000 : ℝ) ≤ X j i ∧ X j i ≤ -(1137/5000 : ℝ)
        else (1541/2500 : ℝ) ≤ X j i ∧ X j i ≤ (6297/5000 : ℝ)) ∧
      (lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3) ∧
      (1 ≤ lpNorm p (X 0 + X 1 + X 2)) ∧
      (lpNorm p (X 0 + X 1 + X 2) < (62967/50000 : ℝ)) ∧
      (((42773/100000 : ℝ)*p)*pairGapSum (lpNorm p) (X 0) (X 1) (X 2) + lpNorm p (X 0 + X 1 + X 2) < 3) ∧
      (∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k →
        lpNorm p (X j + X k) ≤ X j i + X k i + (1/100000000 : ℝ)) ∧
      tripleDeficit p (cyclicConstant p) X < 0 := by sorry
