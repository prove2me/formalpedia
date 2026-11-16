-- Prove2me | Theorems.Thm_GradSuffice_Supplement_theorem_7
-- name    : GradSuffice.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:30:53.640585+00:00
-- url     : https://prove2.me/theorems/247d8b7d-988f-4ad0-ba49-8509a3e93721
-- title:
--   Theorem 7, p.17 — $B$ optimizable ⇔ bounded $(B,B^\star)$-thresholds ⇔ bounded $(B^\star,B^{\star\star})$-thresholds ⇔ $B^\star$ optimizable
-- statement:
--   Let $B$ be the unit ball of a real Banach space $X$, $B^\star$ the unit ball of its dual $X^\star$ and $(B^\star)^\star$ the unit ball of $X^{\star\star}$. The following statements are equivalent:
--
--   1. $B$ is optimizable;
--   2. $(B,B^\star)$-threshold structures are uniformly bounded: for every $\theta>0$ there is $N(\theta)$ such that whenever $(w_i,\xi_i)_{i=1}^N\subseteq B\times B^\star$ satisfy $w_i\cdot\xi_j\le0$ for $i\le j$ and $w_i\cdot\xi_j\ge\theta$ for $i>j$, then $N\le N(\theta)$;
--   3. $(B^\star,(B^\star)^\star)$-threshold structures are uniformly bounded (the same condition with pairs in $B^\star\times(B^\star)^\star$);
--   4. $B^\star$ is optimizable (as the unit ball of the normed space $X^\star$, with objectives convex and 1-Lipschitz for the dual norm and subgradients in $X^{\star\star}$).
--
--   Since threshold structures are self-dual, this transfers optimizability between a space and its dual.
--
--   **Formalization Note** Optimizability is the published `GradSuffice.Optimizable`, applied to $X$ and to $X^\star$ = `StrongDual ℝ X` with the operator norm.
--
--   Differences from the source: none.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), Theorem 7, p.17

import Mathlib
import Definitions.Def_GradSuffice_Optimizable
import Definitions.Def_GradSuffice_Supplement_ThresholdUniformlyBounded

namespace GradSuffice.Supplement

/-- **Theorem 7 (optimizability of the dual).** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, Theorem 7, p.17: "The following statements are
equivalent: 1. `B` is optimizable. 2. `(B, B⋆)`-threshold structures are uniformly bounded.
3. `(B⋆, (B⋆)⋆)`-threshold structures are uniformly bounded. 4. `B⋆` is optimizable."

**Formalization Note.** `B` is the closed unit ball of the real Banach space `X` (standing
assumption, p.3), `B⋆` the closed unit ball of `StrongDual ℝ X` (operator norm = dual norm).
Item 2 is `ThresholdUniformlyBounded X`, item 3 is `ThresholdUniformlyBounded (StrongDual ℝ X)`
(pairs in `B⋆ × (B⋆)⋆`). Item 4 is optimizability of `B⋆` as a domain of the normed space
`StrongDual ℝ X`: objectives are convex and 1-Lipschitz for the dual norm and the oracle returns
subgradients in `(X⋆)⋆`. Optimizability is the paper's randomized notion (base `Optimizable`). -/
theorem theorem_7 (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] :
    List.TFAE
      [ Optimizable X (Metric.closedBall (0 : X) 1),
        ThresholdUniformlyBounded X,
        ThresholdUniformlyBounded (StrongDual ℝ X),
        Optimizable (StrongDual ℝ X) (Metric.closedBall (0 : StrongDual ℝ X) 1) ] := by sorry

end GradSuffice.Supplement
