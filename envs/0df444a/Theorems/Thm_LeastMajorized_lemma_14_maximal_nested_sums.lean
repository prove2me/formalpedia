-- Prove2me | Theorems.Thm_LeastMajorized_lemma_14_maximal_nested_sums
-- name    : LeastMajorized.lemma_14_maximal_nested_sums
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:49:39.292001+00:00
-- url     : https://prove2.me/theorems/6b3ac50e-64ca-484a-bb52-4893e7d135a4
-- title:
--   Lemma 14 — least weakly $(1,b)$-supermajorized elements give maximal nested sums
-- statement:
--   Let $C\subseteq\mathbb R^n$ be closed and bounded. Suppose that for every $b\in\mathbb R^n$ the set $C$ has a least weakly $(1,b)$-supermajorized element. Then for every permutation $\pi$ of $N$ there is a vector $x^*\in C$ whose nested sums along $\pi$ are maximal over $C$:
--
--   $$
--   \sum_{i=1}^k x^*_{\pi(i)}\ \ge\ \sum_{i=1}^k x_{\pi(i)}\qquad\text{for all }x\in C\text{ and all }k\in N .
--   $$
--
--   This is the step (2) ⇒ (4) of the paper's Theorem 1, and the first half of the implication (2) ⇒ (4) of Theorem 5. No convexity of $C$ is assumed.
--
--   Differences from the source:
--   - encoding: closed and bounded C ⊂ ℝⁿ; (1, b) → C : Set (Fin n → ℝ) with IsClosed C and Bornology.IsBounded C; a = fun _ => 1; reason: Lean convention; same instances (⊂ is inclusion, not proper inclusion)
--   - encoding: permutation π of N, Σ_{i=1}^k x_{π(i)} for k ∈ N → π : Equiv.Perm (Fin n), k : Fin n, the sum of x (π i) over i ≤ k; reason: 0-based indices; the paper's k is k.val + 1, and the sets {i ≤ k} for k : Fin n are exactly the paper's {1, …, k}, k ∈ N
-- source:
--   Schoot Uiterkamp, A characterization of simultaneous optimization, majorization, and (bi)submodular polyhedra, arXiv:2201.06596v2, Lemma 14, p.15

import Mathlib
import Definitions.Def_LeastMajorized_IsLeastWeakSuperABMajorized

namespace LeastMajorized

/-- **Lemma 14**, Schoot Uiterkamp, arXiv:2201.06596v2, p.15: "Let `C ⊂ ℝⁿ` be a closed and
bounded set. Suppose that `C` has a least weakly `(1, b)`-supermajorized element for each
`b ∈ ℝⁿ`. Then for each permutation `π` of `N`, there exists a vector `x* ∈ C` such that for all
`x ∈ C` we have `Σ_{i=1}^k x*_{π(i)} ≥ Σ_{i=1}^k x_{π(i)}` for all `k ∈ N`."

**Formalization Note** `ℝⁿ` is `Fin n → ℝ`, `C ⊂ ℝⁿ` means `C ⊆ ℝⁿ`, "bounded" is
`Bornology.IsBounded`. `(1, b)` is `a = fun _ => 1`. A permutation of `N` is
`Equiv.Perm (Fin n)`, 0-based: the paper's index `k ∈ {1, …, n}` is `k : Fin n` with the paper's
`k` equal to `k.val + 1`, and `Σ_{i=1}^k x_{π(i)}` is the sum of `x (π i)` over `i ≤ k`. -/
theorem lemma_14_maximal_nested_sums {n : ℕ} (C : Set (Fin n → ℝ))
    (hC : IsClosed C) (hCb : Bornology.IsBounded C)
    (hleast : ∀ b : Fin n → ℝ, ∃ x, IsLeastWeakSuperABMajorized (fun _ => 1) b C x) :
    ∀ π : Equiv.Perm (Fin n), ∃ xs ∈ C, ∀ x ∈ C, ∀ k : Fin n,
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i ≤ k), x (π i) ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => i ≤ k), xs (π i) := by sorry

end LeastMajorized
