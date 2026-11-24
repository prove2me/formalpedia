-- Prove2me | Theorems.Thm_LinearIdentifiability_diversity_requires_enough_classes
-- name    : LinearIdentifiability.diversity_requires_enough_classes
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T07:38:14.170601+00:00
-- url     : https://prove2.me/theorems/e2c0dc9c-73f9-4055-9760-d779b76179d9
-- title:
--   Section 3.3: the diversity condition with a fixed set of $K$ classes needs $K \ge M+1$
-- statement:
--   Let $M\ge1$, let $g:Y\to\mathbb R^M$, and let $S\subseteq Y$ be a finite set of $K$ classes. If there are $M$ tuples $(y_A^{(i)},y_B^{(i)})$ of elements of $S$ such that the matrix $L$ with columns $g(y_A^{(i)})-g(y_B^{(i)})$ is invertible, then
--
--   $$K\ge M+1.$$
--
--   In supervised classification, where $S$ is the fixed set of all $K$ labels, the diversity condition can therefore only hold when there are more classes than embedding dimensions.
--
--   **Formalization Note** The paper phrases this as the number of classes needed to generate $M$ difference vectors $g(y^{(1)})-g(y^{(j)})$; the statement allows arbitrary tuples in $S$, which includes that case. The hypothesis $M\ge1$ excludes the degenerate case $M=0$, $S=\emptyset$.
-- source:
--   Roeder, Metz and Kingma, On Linear Identifiability of Learned Representations, arXiv:2007.00810v3 (2020), Section 3.3, Discussion of Diversity Condition, p. 5

import Mathlib
import Definitions.Def_LinearIdentifiability_Basic

open Matrix

namespace LinearIdentifiability

theorem diversity_requires_enough_classes {Y : Type*} {M : ℕ} (hM : 0 < M)
    (g : Y → Fin M → ℝ) (S : Finset Y) (a b : Fin M → Y)
    (ha : ∀ i, a i ∈ S) (hb : ∀ i, b i ∈ S) (hL : IsUnit (diffMatrix g a b).det) :
    M + 1 ≤ S.card := by sorry

end LinearIdentifiability
