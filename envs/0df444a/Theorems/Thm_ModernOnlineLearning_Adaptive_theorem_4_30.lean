-- Prove2me | Theorems.Thm_ModernOnlineLearning_Adaptive_theorem_4_30
-- name    : ModernOnlineLearning.Adaptive.theorem_4_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:37:37.206482+00:00
-- url     : https://prove2.me/theorems/47082f58-a75e-401f-b037-a499c7590605
-- title:
--   Theorem 4.30, p. 45 — adaptive OSD regret for self-bounded losses
-- statement:
--   Let $V\subseteq\mathbb R^d$ be nonempty, closed, and convex, with diameter at most $D$. Let $\ell_1,\ldots,\ell_T$ be nonnegative convex losses that are $s$-self-bounded on $V$. Start projected online subgradient descent at any $x_1\in V$; at round $t$ use a subgradient $g_t$ and the adaptive step size $\eta_t=\sqrt2D/(2\sqrt{\sum_{i=1}^t\|g_i\|_2^2})$, leaving the point unchanged when $g_t=0$. For every competitor $u\in V$,
--
--   $$\operatorname{Regret}_T(u)\le4sD^2+2D\sqrt{s\sum_{t=1}^T\ell_t(u)}.$$
--
--   When a competitor incurs zero loss in every round, this gives a regret bound independent of the horizon. The same statement applies to every admissible subgradient and projection choice.
--
--   **Formalization Note** Losses are real-valued and globally nonnegative. Self-boundedness uses the infimum over the full Euclidean space. The diameter is bounded by $D$ rather than defined as an attained maximum; on a nonempty bounded set this lets the theorem use any valid diameter bound. The conditions $T\ge1$ and $s\ge0$ are explicit.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem 4.30, p. 45

import Mathlib
import Definitions.Def_ModernOnlineLearning_Adaptive_Defs

namespace ModernOnlineLearning.Adaptive

/-- Orabona, Theorem 4.30, p. 45. -/
theorem theorem_4_30 {d : ℕ} (V : Set (Vec d)) (ℓ : ℕ → Vec d → ℝ)
    (D s : ℝ) (T : ℕ) (x g : ℕ → Vec d)
    (hT : 1 ≤ T) (hs : 0 ≤ s) (hVne : V.Nonempty)
    (hVclosed : IsClosed V) (hVconv : Convex ℝ V)
    (hdiam : ∀ a ∈ V, ∀ b ∈ V, ‖a - b‖ ≤ D)
    (hconv : ∀ t ∈ Finset.Icc 1 T, ConvexOn ℝ Set.univ (ℓ t))
    (hnonneg : ∀ t ∈ Finset.Icc 1 T, ∀ z : Vec d, 0 ≤ ℓ t z)
    (hself : ∀ t ∈ Finset.Icc 1 T, IsSelfBounded V s (ℓ t))
    (hrun : IsAdaptiveOSDRun V ℓ D T x g) :
    ∀ u ∈ V, regret ℓ x u T ≤
      4 * s * D ^ 2 + 2 * D *
        Real.sqrt (s * (∑ t ∈ Finset.Icc 1 T, ℓ t u)) := by sorry

end ModernOnlineLearning.Adaptive
