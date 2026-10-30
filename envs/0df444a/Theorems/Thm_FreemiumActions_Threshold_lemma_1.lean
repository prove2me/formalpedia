-- Prove2me | Theorems.Thm_FreemiumActions_Threshold_lemma_1
-- name    : FreemiumActions.Threshold.lemma_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T08:57:34.099858+00:00
-- url     : https://prove2.me/theorems/4417dd20-8ecc-4c1e-9e7d-c7b982a747e6
-- title:
--   Lemma 1 — entries of an upper bidiagonal fundamental matrix
-- statement:
--   Let $S=(k_{ij})$ be a real upper bidiagonal square matrix of size $m+1\ge1$ and suppose $1-k_{ii}\ne0$ for every diagonal entry. Its inverse $B=(I-S)^{-1}$ satisfies all three clauses:
--   $$B_{ij}=0\ (j<i),\qquad B_{ii}=\frac1{1-k_{ii}},\qquad B_{ij}=\frac{\prod_{v=i}^{j-1}k_{v,v+1}}{\prod_{v=i}^{j}(1-k_{vv})}\ (i<j).$$
--   For the source’s transient matrix, the nonzero denominators follow from positive quitting. This provides the complete inverse formula, including upper triangularity.
--
--   Differences from the source:
--   - reading: opening prose calls the matrix Q but the displays call it S → S throughout; reason: the displayed matrix and its inverse fix the intended symbol
--   - encoding: one-based matrix of generic size N → zero-based Fin (m+1) indices; reason: m+1 is the matrix size, independently of the model’s largest state label; the successor in the product is used only strictly below its upper endpoint
--   - generalization: upper bidiagonal transient transition matrix → arbitrary real upper bidiagonal matrix with 1-S(i,i) nonzero; reason: every source matrix satisfies these conditions by positive quitting; no probabilistic instance is excluded
-- source:
--   Sheng, Ryan and Nagarajan, Incentivized actions in freemium games, supplied source.pdf dated October 8, 2016, A.2, Lemma 1, p. 30 (PDF p. 30); proof pp. 30–31; catalog DOI 10.1287/msom.2020.0925.

import Mathlib

namespace FreemiumActions.Threshold

theorem lemma_1 (m : ℕ) (S : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hb : ∀ i j, i ≠ j → j.val ≠ i.val + 1 → S i j = 0)
    (hd : ∀ i, 1 - S i i ≠ 0) :
    (∀ i j, j < i → (1 - S)⁻¹ i j = 0) ∧
    (∀ i, (1 - S)⁻¹ i i = 1 / (1 - S i i)) ∧
    (∀ i j, i < j → (1 - S)⁻¹ i j =
      (∏ v ∈ Finset.Ico i j, S v (Fin.ofNat (m + 1) (v.val + 1))) /
        (∏ v ∈ Finset.Icc i j, (1 - S v v))) := by sorry

end FreemiumActions.Threshold
