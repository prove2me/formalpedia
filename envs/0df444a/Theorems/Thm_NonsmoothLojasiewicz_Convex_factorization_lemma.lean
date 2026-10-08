-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Convex_factorization_lemma
-- name    : NonsmoothLojasiewicz.Convex.factorization_lemma
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T18:51:12.755745+00:00
-- url     : https://prove2.me/theorems/f3119b19-44eb-4b6b-8e72-e9653bf0de5f
-- title:
--   Łojasiewicz factorization lemma (recalled in §2.1 from [4, Theorem 6.4])
-- statement:
--   Let $K\subseteq\mathbb R^n$ be compact and let $f,g:K\to\mathbb R$ be continuous subanalytic functions. If $f^{-1}(0)\subseteq g^{-1}(0)$, then there exist $c>0$ and a positive integer $r$ such that
--   $$|g(x)|^{r}\le c\,|f(x)|\qquad\text{for all }x\in K.$$
--
--   This is the classical Łojasiewicz inequality comparing two subanalytic functions with nested zero sets (Bierstone–Milman, *Semianalytic and subanalytic sets*, Theorem 6.4). In the proof of Theorem 3.3 it turns the subanalyticity of $g-\min g$ and $d_S$ into the growth condition $c\,d_S(x)^r\le|g(x)-\min g|$.
--
--   **Formalization Note** $f,g$ are functions on $\mathbb R^n$ of which only the restriction to $K$ matters: they are continuous on $K$ and their graphs over $K$, $\{(x,f(x)):x\in K\}$, are subanalytic subsets of $\mathbb R^n\times\mathbb R$. The page's "(globally)" adds nothing here: a bounded subanalytic set is globally subanalytic, so global subanalyticity is not defined.
-- source:
--   Bolte, Daniilidis & Lewis, SIAM J. Optim. 17 (2007) 1205–1223, p. 1209, Section 2.1, Łojasiewicz factorization lemma (recalled from Bierstone–Milman [4, Theorem 6.4])

import Mathlib
import Definitions.Def_NonsmoothLojasiewicz_Continuous_IsSubanalytic

open Filter Topology

namespace NonsmoothLojasiewicz.Convex

/-- The Łojasiewicz factorization lemma, recalled in Section 2.1 of Bolte–Daniilidis–Lewis
(p. 1209) from Bierstone–Milman [4, Theorem 6.4]: let `K ⊆ ℝⁿ` be compact and `f, g : K → ℝ`
continuous subanalytic functions (their graphs over `K` are subanalytic). If
`f⁻¹(0) ⊆ g⁻¹(0)`, there are `c > 0` and a positive integer `r` with `|g(x)|^r ≤ c |f(x)|` for
all `x ∈ K`. -/
theorem factorization_lemma {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfc : ContinuousOn f K) (hgc : ContinuousOn g K)
    (hfs : NonsmoothLojasiewicz.Continuous.IsSubanalytic {p : EuclideanSpace ℝ (Fin n) × ℝ | p.1 ∈ K ∧ f p.1 = p.2})
    (hgs : NonsmoothLojasiewicz.Continuous.IsSubanalytic {p : EuclideanSpace ℝ (Fin n) × ℝ | p.1 ∈ K ∧ g p.1 = p.2})
    (hzero : ∀ x ∈ K, f x = 0 → g x = 0) :
    ∃ c : ℝ, 0 < c ∧ ∃ r : ℕ, 0 < r ∧ ∀ x ∈ K, |g x| ^ r ≤ c * |f x| := by sorry

end NonsmoothLojasiewicz.Convex
