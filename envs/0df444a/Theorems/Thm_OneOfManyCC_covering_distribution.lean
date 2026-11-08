-- Prove2me | Theorems.Thm_OneOfManyCC_covering_distribution
-- name    : OneOfManyCC.covering_distribution
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:54:33.897245+00:00
-- url     : https://prove2.me/theorems/d8223bad-c1d3-4a8b-9a0d-e99ac7d298e0
-- title:
--   §5, proof of Theorem 1.2 — a distribution $\Lambda$ on solvable rectangles covering every input with probability $\ge 1/2+k^{-2}/4$
-- statement:
--   Let $R$ be a total relation on finite sets and $1\le k\le\min\{|A|,|B|\}$, and put $\delta=1/2+k^{-2}/4$. There is a distribution $\Lambda$ on the set $\mathcal H$ of all solvable rectangles such that, for a random rectangle $A'\times B'$ from $\Lambda$,
--
--   $$\Pr[x\in A']\ge\delta\text{ for every }x\in A,\qquad \Pr[y\in B']\ge\delta\text{ for every }y\in B.$$
--
--   This turns the separate rectangles of Lemma 5.2 into one random rectangle that works for all inputs at once, with an advantage over $1/2$ that majority amplification can use.
--
--   Differences from the source:
--   - encoding: a distribution on a finite set → a point of `stdSimplex ℝ X`, with $\mu(E)$ as `mass μ E`; reason: nonnegative weights summing to one; the probability of an event is the sum of its weights
--   - encoding: $\log$ inside $O(\cdot)$ and $\lceil\log_2\cdot\rceil$ → `Real.logb 2` and `Nat.clog 2`; reason: the paper's logarithms are base 2; `Nat.clog 2 m` is $\lceil\log_2 m\rceil$ for $m\ge1$ and `Real.logb 2 0 = 0`
--   - encoding: finite sets $A, B, O$ → Fintype types in `Type`; reason: every finite set is equivalent to a type in `Type`, and this lets the statement quantify over all of them
--   - encoding: $\mathrm{Inj}_k(A)$ → the embeddings `Fin k ↪ A`; reason: injective maps from $k$ positions are exactly the $k$-tuples of pairwise distinct elements
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), §5, proof of Theorem 1.2, p.11

import Mathlib
import Definitions.Def_OneOfManyCC_Solvable
import Definitions.Def_OneOfManyCC_mass

namespace OneOfManyCC

/-- **The covering distribution.**
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), §5, proof of Theorem 1.2, p.11:
"Hence there is a distribution Λ such that for a random rectangle A′ × B′ from Λ, Pr[x ∈ A′] ≥ δ for
every x ∈ A, Pr[y ∈ B′] ≥ δ for every y ∈ B", with "δ = 1/2 + k⁻²/4" and `Λ` on the set `H` of all
solvable rectangles. -/
theorem covering_distribution {A B O : Type} [Fintype A] [Fintype B] [Fintype O]
    (R : A → B → O → Prop) (hR : IsTotal R) (k : ℕ) (hk₁ : 1 ≤ k)
    (hk : k ≤ min (Fintype.card A) (Fintype.card B)) :
    ∃ Λ ∈ stdSimplex ℝ (SolvableRect k R),
      (∀ x : A, 1 / 2 + (k : ℝ)⁻¹ ^ 2 / 4 ≤ mass Λ {r | x ∈ r.1.1}) ∧
      (∀ y : B, 1 / 2 + (k : ℝ)⁻¹ ^ 2 / 4 ≤ mass Λ {r | y ∈ r.1.2}) := by sorry

end OneOfManyCC
