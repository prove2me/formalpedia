-- Prove2me | Theorems.Thm_HouseAllocLT_LowerBound_lemma_3_2
-- name    : HouseAllocLT.LowerBound.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:04:31.640385+00:00
-- url     : https://prove2.me/theorems/f9f653ac-aa1f-4ac8-9cf6-749b8f1f6892
-- title:
--   Lemma 3.2 — the budget
-- statement:
--   For $n\ge1$, let $\phi$ be a feasible mechanism that is LT on $D_n^n$. Draw each list length independently and uniformly from $[n]$, giving the random profile $\mathbf P$. There exist real numbers $x_1,\ldots,x_n$ satisfying all three conditions
--
--   $$0\le x_j\le\frac1{n-j+1}\quad(1\le j\le n),\qquad \sum_{j=1}^n x_j\le1,\qquad \mathbb E_{\mathbf P}\mathbb E_{\mu\sim\phi(\mathbf P)}|\mu|=\sum_{j=1}^n(n-j+1)x_j.$$
--
--   The budget summarizes the feasible expected output of every such mechanism on the independent-prefix family.
--
--   Differences from the source:
--   - encoding: agents, objects and ranks numbered from one → Fin indices numbered from zero; reason: the bijection sends each code index j to the source index j+1
--   - encoding: lottery on feasible matchings → real probability vector on finite edge sets with feasible support; reason: these encode exactly the same distributions, including irrational weights
--   - encoding: mechanism on the restricted common-prefix report domain → full-domain mechanism with LT required only on the common-prefix domain; reason: arbitrary feasible lotteries extend every restricted mechanism outside that domain, with no extra LT constraint
--   - encoding: expectation over independent uniform list lengths → finite sum divided by n^n; reason: the n^n length vectors have equal mass for positive n
-- source:
--   Jinshan Zhang, Nan Zhao, Hao Xu, Meng Xi, Lin Zhao, STOC 2027 submission #174 (October 2026), Lemma 3.2, equation (3), PDF p. 8 (printed p. 6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/174.pdf

import Definitions.Def_HouseAllocLT_LowerBound_prefixList

open scoped BigOperators ENNReal Topology
open Filter

namespace HouseAllocLT.LowerBound

/-- Lemma 3.2, PDF p.8 (printed p.6), all three parts of equation (3).
The real coefficient n-j.val is paper coefficient n-j+1. -/
theorem lemma_3_2 {n : ℕ} (hn : 1 ≤ n) (φ : Mechanism n n)
    (hφ : IsLTOn φ (prefixDomain n)) :
    ∃ x : Fin n → ℝ,
      (∀ j, 0 ≤ x j ∧ x j ≤ 1 / ((n - j.val : ℕ) : ℝ)) ∧
      (∑ j, x j) ≤ 1 ∧
      profileAverage (fun ℓ => expectedSize φ (prefixProfile ℓ)) =
        ∑ j, ((n - j.val : ℕ) : ℝ) * x j := by sorry

end HouseAllocLT.LowerBound
