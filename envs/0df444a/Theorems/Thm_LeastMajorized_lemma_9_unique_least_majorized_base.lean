-- Prove2me | Theorems.Thm_LeastMajorized_lemma_9_unique_least_majorized_base
-- name    : LeastMajorized.lemma_9_unique_least_majorized_base
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:51:14.757765+00:00
-- url     : https://prove2.me/theorems/605fc53b-d47c-44c6-89df-3cddcb915ea9
-- title:
--   Lemma 9 — $B(f)$ has a unique least $(a,b)$-majorized element; for integral $f,b$ the square-sum minimizers of $B^{\mathbb Z}(f)$ are least $(1,b)$-majorized
-- statement:
--   Let $f:2^N\to\mathbb R$ be submodular. For every scaling vector $a\in\mathbb R^n_{>0}$ and every shifting vector $b\in\mathbb R^n$, the base polyhedron $B(f)$ has exactly one least $(a,b)$-majorized element: there is a unique $x^*\in B(f)$ with
--
--   $$
--   x^*\prec_{(a,b)}y\qquad\text{for all }y\in B(f).
--   $$
--
--   Moreover, if $f$ and $b$ are integral, then every optimal solution of
--
--   $$
--   \min_{x\in B^{\mathbb Z}(f)}\ \sum_{i\in N}\tfrac12(x_i+b_i)^2
--   $$
--
--   is a least $(1,b)$-majorized element of the integral base polyhedron $B^{\mathbb Z}(f)$.
--
--   The paper takes this from Condition 1 and Theorem 1 of Schoot Uiterkamp, Gerards and Hurink (its reference [42]). The first sentence gives the implication (4) ⇒ (1) of Theorem 5; the second is used for the integral Theorem 6.
--
--   Differences from the source:
--   - encoding: a ∈ ℝⁿ_{>0}, "unique" → hypothesis ∀ i, 0 < a i; ∃!; reason: Lean convention; same instances
--   - encoding: f : 2^N → ℝⁿ (typo), submodular with f(∅) = 0 → f : Finset (Fin n) → ℝ with IsSubmodular f; reason: Lean convention; the printed codomain ℝⁿ is a typo for ℝ
--   - encoding: f and b integral, B^ℤ(f) = B(f) ∩ ℤⁿ, optimal solution, (1, b) → ∀ A, ∃ m : ℤ, f A = m; ∀ i, ∃ m : ℤ, b i = m; integralBasePolyhedron f ⊆ Fin n → ℝ; x ∈ B^ℤ(f) with objective at most that of every y ∈ B^ℤ(f); a = fun _ => 1; reason: Lean convention; same instances
-- source:
--   Schoot Uiterkamp, A characterization of simultaneous optimization, majorization, and (bi)submodular polyhedra, arXiv:2201.06596v2, Lemma 9, p.10

import Mathlib
import Definitions.Def_LeastMajorized_IsSubmodular
import Definitions.Def_LeastMajorized_basePolyhedron
import Definitions.Def_LeastMajorized_integralBasePolyhedron
import Definitions.Def_LeastMajorized_IsLeastABMajorized

namespace LeastMajorized

/-- **Lemma 9**, Schoot Uiterkamp, arXiv:2201.06596v2, p.10 (Condition 1 and Theorem 1 of Schoot
Uiterkamp, Gerards, Hurink [42] there): "Let `f` be a submodular function. For each pair of vectors
`a ∈ ℝⁿ_{>0}` and `b ∈ ℝⁿ`, the base polyhedron `B(f)` has a unique least `(a, b)`-majorized
element. Moreover, if `f` and `b` are integral, then any optimal solution to the problem
`min_{x∈B^ℤ(f)} Σ_{i∈N} ½(xᵢ + bᵢ)²` is a least `(1, b)`-majorized element of the integral base
polyhedron `B^ℤ(f)`."

**Formalization Note** `f : Finset (Fin n) → ℝ`; `IsSubmodular` includes `f(∅) = 0`.
`a ∈ ℝⁿ_{>0}` is the hypothesis `∀ i, 0 < a i`. "Unique" is `∃!`. "Integral" means integer-valued
(p.4): every `f A` and every `b i` is the image of an integer. An optimal solution is a point
`x ∈ B^ℤ(f)` with objective value at most that of every `y ∈ B^ℤ(f)`. `(1, b)` is
`a = fun _ => 1`. -/
theorem lemma_9_unique_least_majorized_base {n : ℕ} (f : Finset (Fin n) → ℝ)
    (hf : IsSubmodular f) :
    (∀ a b : Fin n → ℝ, (∀ i, 0 < a i) →
      ∃! x : Fin n → ℝ, IsLeastABMajorized a b (basePolyhedron f) x) ∧
    (∀ b : Fin n → ℝ, (∀ A, ∃ m : ℤ, f A = (m : ℝ)) → (∀ i, ∃ m : ℤ, b i = (m : ℝ)) →
      ∀ x ∈ integralBasePolyhedron f,
        (∀ y ∈ integralBasePolyhedron f,
          ∑ i, (1 / 2 : ℝ) * (x i + b i) ^ 2 ≤ ∑ i, (1 / 2 : ℝ) * (y i + b i) ^ 2) →
        IsLeastABMajorized (fun _ => 1) b (integralBasePolyhedron f) x) := by sorry

end LeastMajorized
