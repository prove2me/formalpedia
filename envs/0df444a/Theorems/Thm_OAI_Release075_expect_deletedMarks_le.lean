-- Prove2me | Theorems.Thm_OAI_Release075_expect_deletedMarks_le
-- name    : OAI.Release075.expect_deletedMarks_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:45:28.711968+00:00
-- url     : https://prove2.me/theorems/6ac8ab05-d6aa-4f22-b28c-64cb77665f17
-- title:
--   Expected number of deleted marks
-- statement:
--   Let $S$ be a finite set of marks in a finite vector space $V$ over a finite field $K$, and let $\omega:S\to\mathbb P(V)$ be a uniformly random direction assignment. A mark is deleted if it lies on an occurring cycle candidate of length $2,\dots,6$ (a cyclic sequence of distinct points whose consecutive pairs are joined by the lines of distinct marks); the others are retained. The degree of a point $z$ counts marks whose line passes through $z\ne$ mark, with mean $\mu(z)=\sum_{a\in S}[z\ne a]/|\mathbb P(V)|$. The exceptional points for a threshold $T$ are the points of degree $<T$ together with all points on lines of deleted marks. Suppose that for every $s\in\{2,\dots,6\}$,
--   $$
--   |V|^s\,|K|^s\,|\mathbb P(V)|^{-s}\le q^{12}.
--   $$
--   Then the expected number of deleted marks is at most $30\,q^{12}$.
--
--   The deletion therefore removes few marks on average once short cycles are rare.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Incidence.lean#L658-L681

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence

open OAI OAI.Release075
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Fintype K] [Fintype V] [Nontrivial V] [Fintype (Projectivization K V)]

theorem OAI.Release075.expect_deletedMarks_le (S : Finset V) (q : ℝ)
    (hcycle : ∀ s ∈ Finset.Icc 2 6,
      (Fintype.card V : ℝ)^s * (Fintype.card K : ℝ)^s *
        (1 / Fintype.card (Projectivization K V) : ℝ)^s ≤ q^12) :
    (𝔼 ω : S → Projectivization K V, ((deletedMarks S ω).card : ℝ)) ≤ 30*q^12 := by sorry
