-- Prove2me | Theorems.Thm_OneOfManyCC_lemma_5_2
-- name    : OneOfManyCC.lemma_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:54:40.128961+00:00
-- url     : https://prove2.me/theorems/b983c6ba-b15a-4410-84fd-17bccb19c276
-- title:
--   Lemma 5.2 — for all $\mu,\nu$, a solvable rectangle has $\mu(A')+\nu(B')\ge 1+k^{-2}$
-- statement:
--   Let $R\subseteq A\times B\times O$ be a total relation on finite sets and let $1\le k\le\min\{|A|,|B|\}$. For every distribution $\mu$ on $A$ and distribution $\nu$ on $B$, some solvable rectangle $A'\times B'$ satisfies
--
--   $$\mu(A')+\nu(B')\ge 1+k^{-2}.$$
--
--   The trivial solvable rectangles $A\times\varnothing$ and $\varnothing\times B$ give exactly $1$, so the lemma asserts a gain above the trivial bound against every pair of distributions. It is the main part of the argument.
--
--   Differences from the source:
--   - encoding: a distribution on a finite set → a point of `stdSimplex ℝ X`, with $\mu(E)$ as `mass μ E`; reason: nonnegative weights summing to one; the probability of an event is the sum of its weights
--   - encoding: $\log$ inside $O(\cdot)$ and $\lceil\log_2\cdot\rceil$ → `Real.logb 2` and `Nat.clog 2`; reason: the paper's logarithms are base 2; `Nat.clog 2 m` is $\lceil\log_2 m\rceil$ for $m\ge1$ and `Real.logb 2 0 = 0`
--   - encoding: finite sets $A, B, O$ → Fintype types in `Type`; reason: every finite set is equivalent to a type in `Type`, and this lets the statement quantify over all of them
--   - encoding: $\mathrm{Inj}_k(A)$ → the embeddings `Fin k ↪ A`; reason: injective maps from $k$ positions are exactly the $k$-tuples of pairwise distinct elements
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), Lemma 5.2, p.10

import Mathlib
import Definitions.Def_OneOfManyCC_Solvable
import Definitions.Def_OneOfManyCC_mass

namespace OneOfManyCC

/-- **Lemma 5.2.**
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), Lemma 5.2, p.10:
"For every distribution µ on A and distribution ν on B, some solvable rectangle A′ × B′ satisfies
µ(A′) + ν(B′) ≥ 1 + k⁻²."

**Formalization Note.** The setting is the standing one of §5: `R` total on finite sets and
`1 ≤ k ≤ min{|A|, |B|}`. -/
theorem lemma_5_2 {A B O : Type} [Fintype A] [Fintype B] [Fintype O] (R : A → B → O → Prop)
    (hR : IsTotal R) (k : ℕ) (hk₁ : 1 ≤ k) (hk : k ≤ min (Fintype.card A) (Fintype.card B))
    (μ : A → ℝ) (hμ : μ ∈ stdSimplex ℝ A) (ν : B → ℝ) (hν : ν ∈ stdSimplex ℝ B) :
    ∃ (A' : Set A) (B' : Set B),
      Solvable k R A' B' ∧ 1 + (k : ℝ)⁻¹ ^ 2 ≤ mass μ A' + mass ν B' := by sorry

end OneOfManyCC
