-- Prove2me | Theorems.Thm_LeastMajorized_lemma_15_submodular_sandwich
-- name    : LeastMajorized.lemma_15_submodular_sandwich
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:49:48.222511+00:00
-- url     : https://prove2.me/theorems/0c4f9581-78c8-43cc-bd41-fcb2b110ddba
-- title:
--   Lemma 15 — maximal nested sums imply $f$ submodular and $B(f)\subseteq\mathrm{co}(C)\subseteq P(f)$
-- statement:
--   Let $C\subseteq\mathbb R^n$ be closed and bounded. Suppose that for every permutation $\pi$ of $N$ there is $x^*\in C$ with $\sum_{i=1}^k x^*_{\pi(i)}\ge\sum_{i=1}^k x_{\pi(i)}$ for all $x\in C$ and all $k\in N$. Then the set function $f(A):=\max_{x\in C}x(A)$ is submodular, and
--
--   $$
--   B(f)\ \subseteq\ \mathrm{co}(C)\ \subseteq\ P(f).
--   $$
--
--   This is the step (4) ⇒ (5) of the paper's Theorem 1; for convex $C$ it gives $B(f)\subseteq C\subseteq P(f)$, the second half of the implication (2) ⇒ (4) of Theorem 5. No convexity of $C$ is assumed.
--
--   Differences from the source:
--   - encoding: f(A) := max_{x∈C} x(A) → maxSetFn C A = sSup {x(A) | x ∈ C}; reason: the hypothesis gives a point of C, so C is nonempty and compact and the supremum is attained: it is the paper's maximum
--   - encoding: closed and bounded C ⊂ ℝⁿ, co(C) → IsClosed C, Bornology.IsBounded C, convexHull ℝ C; reason: Lean convention; same instances
--   - encoding: permutation π of N, Σ_{i=1}^k x_{π(i)} for k ∈ N → π : Equiv.Perm (Fin n), k : Fin n, the sum of x (π i) over i ≤ k; reason: 0-based indices; the sets {i ≤ k} are exactly the paper's {1, …, k}, k ∈ N
-- source:
--   Schoot Uiterkamp, A characterization of simultaneous optimization, majorization, and (bi)submodular polyhedra, arXiv:2201.06596v2, Lemma 15, p.16

import Mathlib
import Definitions.Def_LeastMajorized_IsSubmodular
import Definitions.Def_LeastMajorized_subPolyhedron
import Definitions.Def_LeastMajorized_basePolyhedron
import Definitions.Def_LeastMajorized_maxSetFn

namespace LeastMajorized

/-- **Lemma 15**, Schoot Uiterkamp, arXiv:2201.06596v2, p.16: "Let `C ⊂ ℝⁿ` be a closed and
bounded set. If for each permutation `π` of `N` there exists a vector `x* ∈ C` such that for all
`x ∈ C` we have `Σ_{i=1}^k x*_{π(i)} ≥ Σ_{i=1}^k x_{π(i)}` for all `k ∈ N`, then the set function
`f(A) := max_{x∈C} x(A)` is submodular and we have `B(f) ⊆ co(C) ⊆ P(f)`."

**Formalization Note** `C ⊂ ℝⁿ` means `C ⊆ ℝⁿ` (`Fin n → ℝ`); "bounded" is
`Bornology.IsBounded`; `co(C)` is `convexHull ℝ C`. Permutations are `Equiv.Perm (Fin n)`,
0-based, with the paper's `k` equal to `k.val + 1` and `Σ_{i=1}^k x_{π(i)}` the sum over
`i ≤ k`. `f` is `maxSetFn C`, the `sSup` of `{x(A) | x ∈ C}`; the hypothesis gives a point of
`C` (there is always a permutation), so `C` is nonempty, compact, and the supremum is the
paper's maximum. All three clauses of the conclusion are stated. -/
theorem lemma_15_submodular_sandwich {n : ℕ} (C : Set (Fin n → ℝ))
    (hC : IsClosed C) (hCb : Bornology.IsBounded C)
    (hnest : ∀ π : Equiv.Perm (Fin n), ∃ xs ∈ C, ∀ x ∈ C, ∀ k : Fin n,
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i ≤ k), x (π i) ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => i ≤ k), xs (π i)) :
    IsSubmodular (maxSetFn C) ∧
      basePolyhedron (maxSetFn C) ⊆ convexHull ℝ C ∧
      convexHull ℝ C ⊆ subPolyhedron (maxSetFn C) := by sorry

end LeastMajorized
