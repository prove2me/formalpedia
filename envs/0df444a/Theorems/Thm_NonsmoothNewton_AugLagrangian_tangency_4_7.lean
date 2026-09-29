-- Prove2me | Theorems.Thm_NonsmoothNewton_AugLagrangian_tangency_4_7
-- name    : NonsmoothNewton.AugLagrangian.tangency_4_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:52:00.536429+00:00
-- url     : https://prove2.me/theorems/8af44bc1-dd4f-44df-bbb7-8c96a3f00b12
-- title:
--   Eq. (4.7): limits of directions along the surface are tangent, $\alpha + r\nabla g(\bar x)^{\mathsf T} h = 0$
-- statement:
--   Let $r > 0$, let $g : \mathbb{R}^n \to \mathbb{R}$ be of class $C^2$, and let $(\bar x, \bar s)$ lie on the surface
--   $$
--   \bar s + r g(\bar x) = 0. \tag{4.3}
--   $$
--   Let $h \in \mathbb{R}^n$, $\alpha \in \mathbb{R}$, and let $h_j \to h$, $\alpha_j \to \alpha$ and $t_j \downarrow 0$ (positive, tending to $0$) satisfy
--   $$
--   \bar s + t_j \alpha_j + r g(\bar x + t_j h_j) = 0 \quad \text{for every } j. \tag{4.6}
--   $$
--   Then
--   $$
--   \alpha + r \nabla g(\bar x)^{\mathsf T} h = 0. \tag{4.7}
--   $$
--
--   In the proof of Theorem 4.1 this is what makes the two one-sided limits of $V(h', \alpha')$ agree when the approach to $(\bar x, \bar s)$ crosses the surface: a direction that can be followed along the surface is tangent to it.
--
--   **Formalization Note** "$t_j \downarrow 0$" is `Tendsto tj atTop (𝓝[>] 0)`: $t_j \to 0$ with $t_j > 0$ eventually; monotonicity is not required. $\nabla g(\bar x)^{\mathsf T} h$ is the Fréchet derivative $Dg(\bar x)h$.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), p. 364, Section 4, proof of Theorem 4.1, Eqs. (4.3), (4.6), (4.7)

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_AugLagrangian_SemismoothAt
import Definitions.Def_NonsmoothNewton_AugLagrangian_augLagrangian
open Filter Topology

namespace NonsmoothNewton.AugLagrangian

/-- Qi–Sun (1993), Section 4, Eq. (4.7), p. 364. Let `r > 0`, `g ∈ C²`, and let `(x̄, s̄)` lie on
the surface `s̄ + r g(x̄) = 0` (4.3). If `h_j → h`, `α_j → α`, `t_j ↓ 0` and
`s̄ + t_j α_j + r g(x̄ + t_j h_j) = 0` for every `j` (4.6), then `α + r ∇g(x̄)ᵀ h = 0`. -/
theorem tangency_4_7 {n : ℕ} (r : ℝ) (hr : 0 < r) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : ContDiff ℝ 2 g) (xbar : EuclideanSpace ℝ (Fin n)) (sbar : ℝ)
    (h43 : sbar + r * g xbar = 0)
    (h : EuclideanSpace ℝ (Fin n)) (α : ℝ)
    (hj : ℕ → EuclideanSpace ℝ (Fin n)) (αj tj : ℕ → ℝ)
    (hhj : Tendsto hj atTop (𝓝 h)) (hαj : Tendsto αj atTop (𝓝 α))
    (htj : Tendsto tj atTop (𝓝[>] 0))
    (h46 : ∀ j, sbar + tj j * αj j + r * g (xbar + tj j • hj j) = 0) :
    α + r * fderiv ℝ g xbar h = 0 := by sorry

end NonsmoothNewton.AugLagrangian
