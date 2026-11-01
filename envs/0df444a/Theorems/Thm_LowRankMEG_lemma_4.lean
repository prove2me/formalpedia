-- Prove2me | Theorems.Thm_LowRankMEG_lemma_4
-- name    : LowRankMEG.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:51:22.073225+00:00
-- url     : https://prove2.me/theorems/6d3bc7db-796a-4a63-8b24-c7bd401a5193
-- title:
--   Lemma 4 — warm-start initialization
-- statement:
--   Let $X^*$ be optimal, $r^*=\operatorname{rank}(X^*)$, and let $X\in\mathcal S_n$ with $\operatorname{rank}(X)\ge r^*$. Let $\varepsilon\in(0,3/4]$ and $R>0$. If condition (30) holds, then the matrix $W=(1-\varepsilon)X+\frac\varepsilon nI$ satisfies
--   $$
--   B(X^*,W)\le R^2.
--   $$
--   Moreover, if $\operatorname{rank}(X)=\operatorname{rank}(X^*)$, then condition (31) may replace (30).
--
--   This turns a possibly singular initial matrix into a positive definite first iterate inside the ball of Lemma 3.
--
--   Differences from the source:
--   - encoding: the gradient ∇f → a map grad tied to f by HasFDerivAt at symmetric matrices (Setting.hasGrad); reason: Lean needs ∇f as data; same instances
-- source:
--   Garber & Kaplan, On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for Low-Rank Matrix Optimization, arXiv:2012.10469v2, Lemma 4, p.17

import Mathlib
import Definitions.Def_LowRankMEG_Setting
import Definitions.Def_LowRankMEG_IsOptimal
import Definitions.Def_PSDPolyApprox_densityMatrices
import Definitions.Def_LowRankMEG_bregman
import Definitions.Def_LowRankMEG_InitCond
import Definitions.Def_LowRankMEG_InitCond31

namespace LowRankMEG

/-- **Lemma 4, warm-start initialization**: if `rank(X) ≥ rank(X*)`, `ε ∈ (0, 3/4]`, `R > 0` and (30) holds, then
`W = (1 − ε)X + (ε/n)I` satisfies `B(X*, W) ≤ R²`; if moreover `rank(X) = rank(X*)`, then (31) may replace (30).
Garber & Kaplan, *On the Efficient Implementation of the Matrix Exponentiated Gradient Algorithm for
Low-Rank Matrix Optimization*, arXiv:2012.10469v2, Lemma 4, p.17. -/
theorem lemma_4 {n : ℕ} {f : Matrix (Fin n) (Fin n) ℝ → ℝ}
    {grad : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ} {β : ℝ}
    (hS : Setting f grad β)
    {Xs X : Matrix (Fin n) (Fin n) ℝ} {ε R : ℝ} (hopt : IsOptimal f Xs)
    (hX : X ∈ PSDPolyApprox.densityMatrices n) (hrank : Xs.rank ≤ X.rank)
    (hε : ε ∈ Set.Ioc (0 : ℝ) (3 / 4)) (hR : 0 < R) :
    (InitCond Xs X ε R →
        bregman Xs ((1 - ε) • X + (ε / (n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ)) ≤ R ^ 2) ∧
      (X.rank = Xs.rank → InitCond31 Xs X ε R →
        bregman Xs ((1 - ε) • X + (ε / (n : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℝ)) ≤ R ^ 2) := by sorry

end LowRankMEG
