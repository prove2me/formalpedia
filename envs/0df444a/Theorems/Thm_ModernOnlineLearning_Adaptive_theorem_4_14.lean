-- Prove2me | Theorems.Thm_ModernOnlineLearning_Adaptive_theorem_4_14
-- name    : ModernOnlineLearning.Adaptive.theorem_4_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:37:05.652681+00:00
-- url     : https://prove2.me/theorems/1a10c812-dbd2-491b-8ec5-2f73286d4f60
-- title:
--   Theorem 4.14, p. 40 — adaptive OSD regret in accumulated squared gradient norm
-- statement:
--   Let $V\subseteq\mathbb R^d$ be nonempty, closed, and convex, with $\|a-b\|_2\le D$ for all $a,b\in V$. For $T\ge1$, let $\ell_1,\ldots,\ell_T$ be convex losses, and run projected online subgradient descent from any $x_1\in V$. At round $t$, use a subgradient $g_t$ and step size $\eta_t=\sqrt2D/(2\sqrt{\sum_{i=1}^t\|g_i\|_2^2})$; leave the point unchanged when $g_t=0$. Then every competitor $u\in V$ satisfies
--
--   $$\operatorname{Regret}_T(u)\le D\sqrt{2\sum_{t=1}^T\|g_t\|_2^2}=\sqrt2\min_{\eta>0}\left(\frac{D^2}{2\eta}+\frac\eta2\sum_{t=1}^T\|g_t\|_2^2\right).$$
--
--   The bound adapts to the observed subgradient magnitudes and supplies the first step toward the self-bounded-loss guarantee.
--
--   **Formalization Note** The identity with the *minimum* over constant positive step sizes is stated only when $\sum_t\|g_t\|_2^2>0$, as the existence of a least value of $\eta\mapsto D^2/(2\eta)+(\eta/2)\sum_t\|g_t\|_2^2$ on $(0,\infty)$ whose $\sqrt2$-multiple equals $D\sqrt{2\sum_t\|g_t\|_2^2}$: when every $g_t=0$ the infimum $0$ is not attained, so the printed "min" is not literally true there. Losses are real-valued and subgradients are full-space subgradients. The diameter condition uses $\le D$, as in Theorem 4.14; the run predicate requires $D>0$.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem 4.14, p. 40

import Mathlib
import Definitions.Def_ModernOnlineLearning_Adaptive_Defs

namespace ModernOnlineLearning.Adaptive

/-- Orabona, Theorem 4.14, p. 40: the regret inequality, and the displayed
identity `D√(2Σ‖g_t‖²) = √2 min_{η>0}(D²/(2η) + (η/2)Σ‖g_t‖²)`. The minimum is
attained only when `Σ‖g_t‖² > 0`, so the identity is stated under that case. -/
theorem theorem_4_14 {d : ℕ} (V : Set (Vec d)) (ℓ : ℕ → Vec d → ℝ)
    (D : ℝ) (T : ℕ) (x g : ℕ → Vec d)
    (hT : 1 ≤ T) (hVne : V.Nonempty) (hVclosed : IsClosed V)
    (hVconv : Convex ℝ V)
    (hdiam : ∀ a ∈ V, ∀ b ∈ V, ‖a - b‖ ≤ D)
    (hconv : ∀ t ∈ Finset.Icc 1 T, ConvexOn ℝ Set.univ (ℓ t))
    (hrun : IsAdaptiveOSDRun V ℓ D T x g) :
    (∀ u ∈ V, regret ℓ x u T ≤ D * Real.sqrt (2 * gradientEnergy g T)) ∧
      (0 < gradientEnergy g T → ∃ m : ℝ,
        IsLeast ((fun η : ℝ => D ^ 2 / (2 * η) + η / 2 * gradientEnergy g T) ''
          Set.Ioi 0) m ∧
        D * Real.sqrt (2 * gradientEnergy g T) = Real.sqrt 2 * m) := by sorry

end ModernOnlineLearning.Adaptive
