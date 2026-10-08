-- Prove2me | Theorems.Thm_KleeWalkup67_FiveStep_proposition_3_1
-- name    : KleeWalkup67.FiveStep.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:04:31.211606+00:00
-- url     : https://prove2.me/theorems/8a8249df-8712-4b44-a77b-aa5f427386b7
-- title:
--   3.1 PROPOSITION — facial paths in d-dimensional figures ⇔ avoiding paths in polytopes with 2d + 1 facets ⇔ (1, k₁, …, k_r)-paths in (d+1)-figures
-- statement:
--   Let $d$ and $r$ be positive integers and $k_1,\dots,k_r$ positive integers with $k_i\le d$. The following are equivalent.
--
--   1. **(a)** Given any $d$-dimensional simple Dantzig figure $(P,x,y)$ (bounded or not), the vertices $x$ and $y$ can be joined by a $(k_1,\dots,k_r)$-path.
--   2. **(b)** Given any simple $d$-polytope $P'$ with $2d+1$ facets, two vertices $x,y$ of $P'$ not on the same facet, and a facet $F$ of $P'$ incident to neither $x$ nor $y$, the vertices $x$ and $y$ can be joined by a $(k_1,\dots,k_r)$-path no member of which lies entirely within $F$.
--   3. **(c)** Given any $(d+1)$-dimensional bounded simple Dantzig figure $(Q,u,v)$ and any facet $G$ of $Q$ incident to $u$, the vertices $u$ and $v$ can be joined by a $(1,k_1,\dots,k_r)$-path no member of which lies entirely within $G$.
--
--   The implication (a) $\Rightarrow$ (c) is what transfers facial paths from all $d$-dimensional figures to bounded $(d+1)$-dimensional ones; it turns 3.4(a) into 3.4(b).
--
--   **Formalization Note** Each of (a), (b), (c) quantifies over all presentations in $\mathbb R^d$ (resp. $\mathbb R^{d+1}$), and the theorem asserts $(a\Leftrightarrow b)\wedge(b\Leftrightarrow c)$. The sequence $(k_1,\dots,k_r)$ is a nonempty list. A facet is the face where one row is tight; "incident to $u$" means the row is tight at $u$; "not on the same facet" is disjointness of tight sets.
-- source:
--   Klee & Walkup, The d-step conjecture for polyhedra of dimension d < 6, Acta Math. 117 (1967), p. 65, 3.1 PROPOSITION; proof pp. 65–66

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_walk
import Definitions.Def_KleeWalkup67_FiveStep_Polyhedra

open scoped RealInnerProductSpace

namespace KleeWalkup67.FiveStep

/-- 3.1 PROPOSITION, p. 65: for positive `d` and a nonempty list `ks = (k₁, …, k_r)` of positive
integers `k_i ≤ d`, statements (a), (b), (c) are equivalent. -/
theorem proposition_3_1 (d : ℕ) (hd : 0 < d) (ks : List ℕ) (hks : ks ≠ [])
    (hk : ∀ k ∈ ks, 0 < k ∧ k ≤ d) :
    let A : Prop :=
      ∀ (a : Fin (2 * d) → EuclideanSpace ℝ (Fin d)) (b : Fin (2 * d) → ℝ)
        (x y : EuclideanSpace ℝ (Fin d)),
        IsDantzigFigure a b x y → IsSimple a b → IsFacialPath a b ks x y
    let B : Prop :=
      ∀ (a : Fin (2 * d + 1) → EuclideanSpace ℝ (Fin d)) (b : Fin (2 * d + 1) → ℝ),
        IsFacetPresentation a b → Bornology.IsBounded (Hirsch.Hpoly a b) → IsSimple a b →
        ∀ x ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
        ∀ y ∈ Set.extremePoints ℝ (Hirsch.Hpoly a b),
          Disjoint (TightSet a b x) (TightSet a b y) →
          ∀ i, i ∉ TightSet a b x → i ∉ TightSet a b y →
            IsFacialPathAvoiding a b ks x y (faceOf a b {i})
    let C : Prop :=
      ∀ (a : Fin (2 * (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))) (b : Fin (2 * (d + 1)) → ℝ)
        (u v : EuclideanSpace ℝ (Fin (d + 1))),
        IsDantzigFigure a b u v → IsSimple a b → Bornology.IsBounded (Hirsch.Hpoly a b) →
        ∀ i ∈ TightSet a b u, IsFacialPathAvoiding a b (1 :: ks) u v (faceOf a b {i})
    (A ↔ B) ∧ (B ↔ C) := by sorry

end KleeWalkup67.FiveStep
