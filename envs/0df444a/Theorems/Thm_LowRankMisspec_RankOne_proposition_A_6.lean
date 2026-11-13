-- Prove2me | Theorems.Thm_LowRankMisspec_RankOne_proposition_A_6
-- name    : LowRankMisspec.RankOne.proposition_A_6
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-10T23:14:39.381016+00:00
-- url     : https://prove2.me/theorems/07f2cfa7-95df-4dfe-b8fb-77c7e016408e
-- title:
--   Proposition A.6 — a rank-one nonnegative matrix with entry sum 1 is the product of its row and column sums
-- statement:
--   Let $A$ be a real matrix with finite row and column index sets, nonnegative entries and $\sum_{i,j}A[i,j]=1$. If $\operatorname{rank}(A)=1$, then every entry equals its row sum times its column sum:
--   $$A[i,j]=\Big(\sum_k A[i,k]\Big)\Big(\sum_\ell A[\ell,j]\Big).$$
--   This is the step that turns rank one of each $J_t(P)$ into the factorization $P[hf]=P^{(t)}[h]\cdot\Pr[X_{t+1:T}=f]$ in Proposition A.7.
--
--   Differences from the source:
--   - encoding: a matrix A (finite index sets) → A : Matrix m n ℝ with [Fintype m] [Fintype n], m n : Type; reason: any finite index sets; the universe level changes no instance
-- source:
--   Hasrati, Risteski, Understanding Model Misspecification in Low-Rank Distributions: Tolerant Testing and Agnostic Learning, STOC 2027 submission (manuscript sha256 235f2a4f…), p. 15 (PDF 16), Proposition A.6

import Mathlib

namespace LowRankMisspec.RankOne

/-- Proposition A.6 (entries of a rank-one probability matrix): a real matrix with nonnegative
entries summing to `1` and rank exactly `1` has every entry equal to its row sum times its column
sum. -/
theorem proposition_A_6 {m n : Type} [Fintype m] [Fintype n] (A : Matrix m n ℝ)
    (hnonneg : ∀ i j, 0 ≤ A i j) (hsum : ∑ i, ∑ j, A i j = 1) (hrank : A.rank = 1) :
    ∀ i j, A i j = (∑ k, A i k) * (∑ l, A l j) := by sorry

end LowRankMisspec.RankOne
