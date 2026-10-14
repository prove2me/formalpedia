-- Prove2me | Theorems.Thm_OfflineStochMatch_UnitPatience_lemma_8
-- name    : OfflineStochMatch.UnitPatience.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:32.133093+00:00
-- url     : https://prove2.me/theorems/3d32a1d7-610b-4ac4-ac61-7bac1c20508c
-- title:
--   Lemma 8, p. 17 — Σ w_i z_i ∏_{j<i}(1 − z_j) ≥ (1 − 1/e) Σ w_i z_i for Σ z_i ≤ 1 and w decreasing, ≥ 0
-- statement:
--   For $i\in[k]$ let $z_i\in[0,1]$ with $\sum_{i=1}^{k}z_i\le 1$, and let $w_1\ge w_2\ge\cdots\ge w_k\ge 0$. Then
--   $$\sum_{i=1}^{k}w_iz_i\prod_{j=1}^{i-1}(1-z_j)\ \ge\ \Big(1-\frac1e\Big)\sum_{i=1}^{k}w_iz_i.\tag{26}$$
--
--   This deterministic inequality says that greedy-by-weight on independent edges with total activation probability at most one collects a $(1-1/e)$ fraction of the fractional value; combined with Lemma 7 it yields Lemma 9.
--
--   **Formalization Note** The page's $w_i\in\mathbb R^+$ is read as $w_i\ge 0$ (the proof uses only $w_k-w_{k+1}=w_k\ge 0$). The sequences are indexed by $\mathbb N$ and only the indices $1,\dots,k$ are constrained. $1-1/e$ is written $1-e^{-1}$.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, p. 17, Lemma 8, Eq. (26)

import Mathlib
import Definitions.Def_OfflineStochMatch_UnitPatience_Setting

namespace OfflineStochMatch.UnitPatience

open Finset

theorem lemma_8 (k : ℕ) (z w : ℕ → ℝ) (hz : ∀ i ∈ Icc 1 k, 0 ≤ z i ∧ z i ≤ 1)
    (hsum : ∑ i ∈ Icc 1 k, z i ≤ 1) (hw : ∀ i ∈ Icc 1 k, 0 ≤ w i)
    (hmono : ∀ i ∈ Icc 1 k, ∀ j ∈ Icc 1 k, i ≤ j → w j ≤ w i) :
    (1 - Real.exp (-1)) * ∑ i ∈ Icc 1 k, w i * z i
      ≤ ∑ i ∈ Icc 1 k, w i * z i * ∏ j ∈ Ico 1 i, (1 - z j) := by sorry

end OfflineStochMatch.UnitPatience
