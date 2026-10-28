-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_affineMaximum_coercive_readable
-- name    : FunctionalInequalities.Analysis.affineMaximum_coercive_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:26.694089+00:00
-- url     : https://prove2.me/theorems/e32066d6-367b-466d-9089-f5d72ac05f70
-- title:
--   Coercive Lower Bound for a Finite Affine Maximum
-- statement:
--   This is a geometric coercivity statement for a finite affine maximum.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $s\subseteq E$ be a nonempty finite set, and assume
--
--   $$0\in\operatorname{int}\bigl(\operatorname{conv}(s)\bigr).$$
--
--   Then there exists $c>0$ such that, for every function $a:E\to\mathbb R$, every $M\in\mathbb R$, and every $y\in E$, if $a(x)\le M$ for all $x\in s$, then
--
--   $$c\|y\|-M\le \operatorname{affineMaximum}(s,a,y),$$
--
--   where `affineMaximum` is the maximum of $\langle x,y\rangle-a(x)$ over $x\in s$. The constant $c$ depends on the finite set and its neighborhood condition, but not on $a$, $M$, or $y$. The vertex intercept bound is required only on the elements of $s$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem affineMaximum_coercive [FiniteDimensional ℝ E]
--       (s : Finset E) (hs : s.Nonempty)
--       (h0 : (0 : E) ∈ interior (convexHull ℝ (↑s : Set E))) :
--       ∃ c : ℝ, 0 < c ∧ ∀ (a : E → ℝ) (M : ℝ), (∀ x ∈ s, a x ≤ M) →
--         ∀ y, c * ‖y‖ - M ≤ affineMaximum s hs a y
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/AffineMaximum`](https://prove2.me/theorems/6ce50813-8eec-46a5-abb0-e806e1385307).
--
--   Next: [`eventually_affineMaximum_sub_le_legendre`](https://prove2.me/theorems/5b6258b4-53ab-4ec0-9b82-126b22c2ab6c).
--
--   [Source excerpt, lines 53–57](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/AffineMaximum.lean#L53-L57) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/AffineMaximum.lean#L51-L98 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.AffineMaximum`, declaration `FunctionalInequalities.Analysis.affineMaximum_coercive`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_AffineMaximum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.affineMaximum_coercive_readable [FiniteDimensional ℝ E]
    (s : Finset E) (hs : s.Nonempty)
    (h0 : (0 : E) ∈ interior (convexHull ℝ (↑s : Set E))) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : E → ℝ) (M : ℝ), (∀ x ∈ s, a x ≤ M) →
      ∀ y, c * ‖y‖ - M ≤ affineMaximum s hs a y := by sorry
