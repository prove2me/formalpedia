-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Continuous_curve_selection
-- name    : NonsmoothLojasiewicz.Continuous.curve_selection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:13:32.799666+00:00
-- url     : https://prove2.me/theorems/9c58de55-97f5-4075-a0ce-19b818419b7a
-- title:
--   Curve selection lemma (recalled in §2.1 from [4, Lemma 6.3])
-- statement:
--   Let $A$ be a subanalytic subset of $\mathbb{R}^n$ and let $a$ be a point of its boundary $\operatorname{bd} A = \overline{A} \setminus \operatorname{int} A$. Then there exists a real-analytic path $z : (-1, 1) \to \mathbb{R}^n$ such that
--   $$
--   z(0) = a \qquad \text{and} \qquad z\big((0, 1)\big) \subseteq A .
--   $$
--
--   The curve selection lemma turns a point in the closure of a subanalytic set into an analytic arc entering the set, which reduces several limiting statements to one-variable analysis. The proof of Theorem 3.1 uses it twice.
--
--   **Formalization Note.** The path is a function `z : ℝ → ℝⁿ` that is real-analytic in a neighbourhood of every point of $(-1, 1)$ (`AnalyticOnNhd ℝ z (Set.Ioo (-1) 1)`); its values outside $(-1, 1)$ play no role. The boundary is Mathlib's `frontier`.
-- source:
--   Bolte, Daniilidis & Lewis, SIAM J. Optim. 17 (2007) 1205–1223, p. 1208 (PDF p. 4), Section 2.1, curve selection lemma (recalled from [4, Lemma 6.3], Bierstone & Milman, Semianalytic and subanalytic sets)

import Mathlib
import Definitions.Def_NonsmoothLojasiewicz_Continuous_IsSubanalytic

open Filter Topology
open scoped ENNReal

namespace NonsmoothLojasiewicz.Continuous

/-- Curve selection lemma (recalled in §2.1, p. 1208, from [4, Lemma 6.3]): if `A ⊆ ℝⁿ` is
subanalytic and `a` lies in the boundary `bd A`, there is an analytic path `z : (−1, 1) → ℝⁿ`
with `z(0) = a` and `z((0, 1)) ⊆ A`. The path is a function `ℝ → ℝⁿ` real-analytic on a
neighbourhood of every point of `(−1, 1)`; its values off `(−1, 1)` are irrelevant. -/
theorem curve_selection {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n))) (hA : IsSubanalytic A)
    (a : EuclideanSpace ℝ (Fin n)) (ha : a ∈ frontier A) :
    ∃ z : ℝ → EuclideanSpace ℝ (Fin n), AnalyticOnNhd ℝ z (Set.Ioo (-1) 1) ∧ z 0 = a ∧
      z '' Set.Ioo 0 1 ⊆ A := by sorry

end NonsmoothLojasiewicz.Continuous
