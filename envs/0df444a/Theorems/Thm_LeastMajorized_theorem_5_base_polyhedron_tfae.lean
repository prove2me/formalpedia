-- Prove2me | Theorems.Thm_LeastMajorized_theorem_5_base_polyhedron_tfae
-- name    : LeastMajorized.theorem_5_base_polyhedron_tfae
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:50:02.285552+00:00
-- url     : https://prove2.me/theorems/9acf7f44-14d4-4f1f-b463-509041d157a8
-- title:
--   Theorem 5 — a compact convex set has least $(a,b)$-majorized elements for all $(a,b)$ iff it is a base polyhedron
-- statement:
--   Let $C\subseteq\mathbb R^n$ be a compact convex set. The following statements are equivalent:
--
--   1. $C$ has a least $(a,b)$-majorized element for each $a\in\mathbb R^n_{>0}$ and $b\in\mathbb R^n$;
--   2. $C$ has a least $(1,b)$-majorized element for each $b\in\mathbb R^n$;
--   3. for each $b\in\mathbb R^n$ there is a single $x^*\in C$ that is an optimal solution of
--   $$
--   \min_{x\in C}\ \Phi(x+b)
--   $$
--   for every continuous Schur-convex function $\Phi:\mathbb R^n\to\mathbb R$;
--   4. the set function $f(A):=\max_{x\in C}x(A)$ is submodular and $C=B(f)$.
--
--   This is the paper's characterization of base polyhedra: among compact convex sets, base polyhedra of submodular functions are exactly the sets on which, for every shift $b$, one point minimizes all symmetric (Schur-convex) objectives of $x+b$ simultaneously. It explains why resource allocation problems over sets that are not base polyhedra force trade-offs between such objectives.
--
--   Differences from the source:
--   - reading: "there exists x* ∈ C that is an optimal solution to min_{x∈C} Φ(x + b) for any choice of continuous Schur-convex function Φ" → ∀ b, ∃ x* ∈ C, ∀ Φ continuous Schur-convex, ∀ y ∈ C, Φ(x* + b) ≤ Φ(y + b); reason: one x* for all Φ is the paper's simultaneous optimization (title; remark at the end of §3.2, p.10); the other order ∀ Φ ∃ x* holds for every compact C and would make the equivalence false
--   - encoding: f(A) := max_{x∈C} x(A) → maxSetFn C A = sSup {x(A) | x ∈ C}; reason: for nonempty compact C the supremum is attained, so it is the paper's maximum; for C = ∅ all four statements are false in Lean (statement 4 because 0 ∈ B(maxSetFn ∅)), so the equivalence is unaffected
--   - encoding: compact convex C ⊂ ℝⁿ, a ∈ ℝⁿ_{>0}, (1, b) → C : Set (Fin n → ℝ) with IsCompact C and Convex ℝ C; ∀ i, 0 < a i; a = fun _ => 1; reason: Lean convention; same instances (⊂ is inclusion)
--   - encoding: Schur-convex with respect to x ≺ y → SchurConvex Φ with respect to the published RetailVariety.Fashion.Majorized; reason: the same relation (see LeastMajorized.SchurConvex)
-- source:
--   Schoot Uiterkamp, A characterization of simultaneous optimization, majorization, and (bi)submodular polyhedra, arXiv:2201.06596v2, Theorem 5, §5.3, p.18

import Mathlib
import Definitions.Def_LeastMajorized_IsSubmodular
import Definitions.Def_LeastMajorized_basePolyhedron
import Definitions.Def_LeastMajorized_maxSetFn
import Definitions.Def_LeastMajorized_SchurConvex
import Definitions.Def_LeastMajorized_IsLeastABMajorized

namespace LeastMajorized

/-- **Theorem 5**, Schoot Uiterkamp, *A characterization of simultaneous optimization,
majorization, and (bi)submodular polyhedra*, arXiv:2201.06596v2, §5.3, p.18: "Let `C ⊂ ℝⁿ` be a
compact convex set. The following statements are equivalent:
1. `C` has a least `(a, b)`-majorized element for each `a ∈ ℝⁿ_{>0}` and `b ∈ ℝⁿ`;
2. `C` has a least `(1, b)`-majorized element for each `b ∈ ℝⁿ`;
3. For each `b ∈ ℝⁿ`, there exists `x* ∈ C` that is an optimal solution to `min_{x∈C} Φ(x + b)`
   for any choice of continuous Schur-convex function `Φ`;
4. The function `f(A) := max_{x∈C} x(A)` is submodular and `C = B(f)`."

**Formalization Note** `ℝⁿ` is `Fin n → ℝ`; `C ⊂ ℝⁿ` means `C ⊆ ℝⁿ`. `a ∈ ℝⁿ_{>0}` is
`∀ i, 0 < a i`; `(1, b)` is `a = fun _ => 1`. In statement 3 one `x*` (chosen for `b`) serves
every continuous Schur-convex `Φ` simultaneously (`∀ b, ∃ x*, ∀ Φ`), and "optimal solution to
`min_{x∈C} Φ(x + b)`" is `x* ∈ C ∧ ∀ y ∈ C, Φ(x* + b) ≤ Φ(y + b)`. Schur-convexity is with
respect to the published `RetailVariety.Fashion.Majorized`. `f` is `maxSetFn C` (`sSup` of
`{x(A) | x ∈ C}`, the maximum for nonempty compact `C`). `C` is not assumed nonempty: for
`C = ∅` all four statements are false. -/
theorem theorem_5_base_polyhedron_tfae {n : ℕ} (C : Set (Fin n → ℝ))
    (hC : IsCompact C) (hconv : Convex ℝ C) :
    List.TFAE
      [∀ a b : Fin n → ℝ, (∀ i, 0 < a i) → ∃ x, IsLeastABMajorized a b C x,
       ∀ b : Fin n → ℝ, ∃ x, IsLeastABMajorized (fun _ => 1) b C x,
       ∀ b : Fin n → ℝ, ∃ x ∈ C, ∀ Φ : (Fin n → ℝ) → ℝ, Continuous Φ → SchurConvex Φ →
         ∀ y ∈ C, Φ (x + b) ≤ Φ (y + b),
       IsSubmodular (maxSetFn C) ∧ C = basePolyhedron (maxSetFn C)] := by sorry

end LeastMajorized
