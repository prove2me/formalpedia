-- Prove2me | Theorems.Thm_LostSalesLearning_ValueGap_fullState_dominates
-- name    : LostSalesLearning.ValueGap.fullState_dominates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T10:18:38.96899+00:00
-- url     : https://prove2.me/theorems/a26af067-2c2c-4674-b9b4-c535f2bf1d6b
-- title:
--   Proof of Lemma 2.5, p. 9 — ŝ := (x, 0, …, 0) ⪰ s for all states s ∈ S^x
-- statement:
--   Let $L\ge 1$ and let $\hat{\mathbf s}=(x,0,0,\dots,0)\in\mathbb R^{L+1}$ be the state with all inventory on hand and nothing on order. Then for every state $\mathbf s\in\mathcal S^x$,
--   $$\hat{\mathbf s}\succeq\mathbf s .$$
--
--   This is the observation of the proof of Lemma 2.5 that lets Lemmas B.6 and B.7 compare every state with the single reference state $\hat{\mathbf s}$.
--
--   **Formalization Note** The order is Definition B.1 (`Dominates (fullState L x) s`). The hypothesis $L\ge 1$ is needed: Definition B.1 asks for a split index $0\le k\le L-1$, which does not exist when $L=0$.
-- source:
--   Agrawal & Jia, Learning in Structured MDPs with Convex Cost Functions, arXiv:1905.04337v1, p. 9, proof of Lemma 2.5, sentence before the first display

import Mathlib
import Definitions.Def_LostSalesLearning_ValueGap_Setting

open MeasureTheory
open scoped NNReal

namespace LostSalesLearning.ValueGap

theorem fullState_dominates {L : ℕ} (hL : 1 ≤ L) (x : ℝ) (s : Fin (L + 1) → ℝ)
    (hs : s ∈ Sx L x) :
    Dominates (fullState L x) s := by sorry

end LostSalesLearning.ValueGap
