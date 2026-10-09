-- Prove2me | Theorems.Thm_ModernOnlineLearning_Adaptive_implicit_bound
-- name    : ModernOnlineLearning.Adaptive.implicit_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:38:39.95525+00:00
-- url     : https://prove2.me/theorems/2360383e-e49d-4c99-9dee-6637a3db5cd4
-- title:
--   Section 4.2.3, p. 45 — implicit regret bound for self-bounded losses
-- statement:
--   Under Theorem 4.30's assumptions, let $x_t$ be any adaptive OSD run on nonnegative, convex, $s$-self-bounded losses over a nonempty closed convex set of diameter at most $D$. Then, for every $u\in V$,
--
--   $$\operatorname{Regret}_T(u)\le 2D\sqrt{s\sum_{t=1}^T\ell_t(x_t)}.$$
--
--   This is the implicit inequality preceding Lemma 4.29: the cumulative loss of the algorithm still appears on the right-hand side.
--
--   **Formalization Note** Self-boundedness is checked at every feasible point and for every full-space subgradient, with the loss infimum taken over all of $\mathbb R^d$. Losses are real-valued and globally nonnegative; $T\ge1$ and $s\ge0$ are explicit.
-- source:
--   Orabona, arXiv:1912.13213v10, §4.2.3, display before Lemma 4.29, p. 45

import Mathlib
import Definitions.Def_ModernOnlineLearning_Adaptive_Defs

namespace ModernOnlineLearning.Adaptive

/-- The implicit regret bound displayed immediately before Lemma 4.29 on p. 45. -/
theorem implicit_bound {d : ℕ} (V : Set (Vec d)) (ℓ : ℕ → Vec d → ℝ)
    (D s : ℝ) (T : ℕ) (x g : ℕ → Vec d)
    (hT : 1 ≤ T) (hs : 0 ≤ s) (hVne : V.Nonempty)
    (hVclosed : IsClosed V) (hVconv : Convex ℝ V)
    (hdiam : ∀ a ∈ V, ∀ b ∈ V, ‖a - b‖ ≤ D)
    (hconv : ∀ t ∈ Finset.Icc 1 T, ConvexOn ℝ Set.univ (ℓ t))
    (hnonneg : ∀ t ∈ Finset.Icc 1 T, ∀ z : Vec d, 0 ≤ ℓ t z)
    (hself : ∀ t ∈ Finset.Icc 1 T, IsSelfBounded V s (ℓ t))
    (hrun : IsAdaptiveOSDRun V ℓ D T x g) :
    ∀ u ∈ V, regret ℓ x u T ≤
      2 * D * Real.sqrt (s * (∑ t ∈ Finset.Icc 1 T, ℓ t (x t))) := by sorry

end ModernOnlineLearning.Adaptive
