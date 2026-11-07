-- Prove2me | Theorems.Thm_LosslessCond_lemma_4_2
-- name    : LosslessCond.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:33:45.192892+00:00
-- url     : https://prove2.me/theorems/bbff2925-a098-4ed8-991d-57f6d88e2cc2
-- title:
--   Lemma 4.2 — leaf conditions: at most $r$ row requirements and at most $2(r+1)^{r+1}$ conditions
-- statement:
--   Let $M:X\times Y\to\{0,1\}$ be a finite Boolean matrix with $\operatorname{rank}(M)\le r$ over $\mathbb R$, for an integer $r\ge 1$. For $b\in\{0,1\}$ and $U\subseteq X$, the **leaf condition** of $(b,U)$ is the column set
--   $$
--   L_b(U)=\{y\in Y:\ M(x,y)=b\ \text{for every } x\in U\}.
--   $$
--
--   1. Every leaf condition is defined by at most $r$ of its row requirements: there is $U'\subseteq U$ with $|U'|\le r$ and $L_b(U')=L_b(U)$.
--   2. Including both outputs and all row sets, the number of different leaf conditions is at most
--   $$
--   \bigl|\{(b,L_b(U)):\ b\in\{0,1\},\ U\subseteq X\}\bigr|\le 2(r+1)^{r+1}.
--   $$
--
--   The count does not depend on $|X|$ or $|Y|$; it is the per-leaf factor in the domain count of Lemma 4.3.
--
--   Differences from the source:
--   - encoding: at most r distinct row-value requirements → a set U' ⊆ U of at most r row labels defining the same condition; reason: requirements on r distinct row values are requirements on r labels (one per value) and conversely
--   - reading: the number of different leaf conditions, including both possible outputs → the number of pairs (b, L_b(U)); reason: the proof adds the counts for the two outputs; pairs are at least as many as column sets, so this is the stronger reading
--   - generalization: finite nonempty input sets X, Y → finite types X Y : Type (Fintype), nonemptiness not assumed; reason: every finite nonempty set is equivalent to a type in universe 0, so every instance of the source is covered; the instances with an empty X or Y are additional, and there the statement holds trivially
-- source:
--   Mackenzie, Lossless Hardness Condensation in Deterministic Communication Complexity, arXiv:2609.28691 (held version, sha256 ce75e6d41cda6fdcdc55c619ab80e2b628e40845768cc3021cc0a0bfe7743fcf), Lemma 4.2, p.11 (PDF p.12)

import Mathlib
import Definitions.Def_DetCCHard_realRank

namespace LosslessCond

/-- **Lemma 4.2 (Leaf conditions)** (Mackenzie, *Lossless Hardness Condensation in Deterministic
Communication Complexity*, arXiv:2609.28691, held version sha256 ce75e6d4…, p.11). Suppose
`rank(M) ≤ r` for an integer `r ≥ 1`. Every same-answer leaf condition
`{y : M(x, y) = b for every x ∈ U}` is equivalent, on the actual column set, to at most `r`
distinct row-value requirements. Including both possible outputs and all retained row sets, the
number of different leaf conditions is at most `2(r + 1)^(r+1)`.

**Formalization Note** The first clause gives at most `r` rows `U' ⊆ U` (a `Finset` of original
labels) whose requirements define the same set of columns as those of `U`; requirements on at most
`r` distinct row values are the same as requirements on at most `r` row labels. The count is of
the pairs `(b, condition)` over `b ∈ {0, 1}` and all `U ⊆ X` (the proof adds the counts of the two
outputs); this is at least the number of distinct column sets. The set of pairs is finite since
`Y` is, so `Set.ncard` is its true size. -/
theorem lemma_4_2 {X Y : Type} [Fintype X] [Fintype Y] (M : X → Y → Bool) (r : ℕ) (hr : 1 ≤ r)
    (hrank : DetCCHard.realRank M ≤ r) :
    (∀ (b : Bool) (U : Set X), ∃ U' : Finset X, ↑U' ⊆ U ∧ U'.card ≤ r ∧
      {y | ∀ x ∈ (U' : Set X), M x y = b} = {y | ∀ x ∈ U, M x y = b}) ∧
    {p : Bool × Set Y | ∃ (b : Bool) (U : Set X), p = (b, {y | ∀ x ∈ U, M x y = b})}.ncard ≤
      2 * (r + 1) ^ (r + 1) := by sorry

end LosslessCond
