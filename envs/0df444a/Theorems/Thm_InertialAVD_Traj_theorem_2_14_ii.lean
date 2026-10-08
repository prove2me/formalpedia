-- Prove2me | Theorems.Thm_InertialAVD_Traj_theorem_2_14_ii
-- name    : InertialAVD.Traj.theorem_2_14_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:09:14.087985+00:00
-- url     : https://prove2.me/theorems/e34357ed-2df2-4929-8640-93215e797575
-- title:
--   Theorem 2.14 ii) with (15) — for $\alpha>3$, $x$ is bounded by (15) and $\int_{t_0}^{\infty}t\|\dot x\|^2dt\le\mathcal E_{2,2(\alpha-3)}(t_0)/(\alpha-3)$
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $\Phi:\mathcal H\to\mathbb R$ convex and continuously differentiable, $x^*\in\operatorname{argmin}\Phi$, $\alpha>3$, $t_0>0$, and let $x$ be a solution of $\ddot x+\frac{\alpha}{t}\dot x+\nabla\Phi(x)=0$ on $[t_0,+\infty[$. Let $\mathcal E_{2,2(\alpha-3)}$ be the anchored energy
--   $$\mathcal E_{2,2(\alpha-3)}(t)=t^2(\Phi(x(t))-\Phi(x^*))+\tfrac12\|2(x(t)-x^*)+t\dot x(t)\|^2+(\alpha-3)\|x(t)-x^*\|^2.$$
--   Then $x$ is bounded on $[t_0,+\infty[$; more precisely, for every $t\ge t_0$,
--   $$\|x(t)-x^*\|^2\le\frac{\mathcal E_{2,2(\alpha-3)}(t)}{\alpha-3}\le\frac{\mathcal E_{2,2(\alpha-3)}(t_0)}{\alpha-3}, \tag{15}$$
--   and $t\mapsto t\|\dot x(t)\|^2$ is integrable on $]t_0,+\infty[$ with
--   $$\int_{t_0}^{+\infty}t\|\dot x(t)\|^2\,dt\le\frac{\mathcal E_{2,2(\alpha-3)}(t_0)}{\alpha-3}<+\infty. \tag{13}$$
--
--   The integrability of $t\|\dot x\|^2$ is the key estimate for the weak convergence of the trajectories (Theorem 2.16).
--
--   **Formalization Note** The finiteness "$<+\infty$" of (13) is stated as Lebesgue integrability on $]t_0,+\infty[$, together with the bound on the integral; boundedness of $x$ is stated as boundedness of $x([t_0,+\infty[)$.
-- source:
--   Attouch, Chbani, Peypouquet, Redont, Fast convergence of inertial dynamics and algorithms with asymptotic vanishing damping, Optimization Online preprint 5179 (Oct. 2015), p. 7, Theorem 2.14 ii), (13), and (15) in its proof

import Mathlib
import Definitions.Def_InertialAVD_Traj_Setting

open MeasureTheory

namespace InertialAVD.Traj

theorem theorem_2_14_ii {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (Φ : H → ℝ) (hΦconv : ConvexOn ℝ Set.univ Φ) (hΦC1 : ContDiff ℝ 1 Φ)
    (α t₀ : ℝ) (hα : 3 < α) (x v : ℝ → H) (hsol : IsSolution Φ α t₀ x v)
    (xstar : H) (hxstar : ∀ y : H, Φ xstar ≤ Φ y) :
    Bornology.IsBounded (x '' Set.Ici t₀) ∧
    (∀ t ∈ Set.Ici t₀,
      ‖x t - xstar‖ ^ 2 ≤ anchoredEnergy Φ x v 2 (2 * (α - 3)) xstar t / (α - 3) ∧
      anchoredEnergy Φ x v 2 (2 * (α - 3)) xstar t / (α - 3)
        ≤ anchoredEnergy Φ x v 2 (2 * (α - 3)) xstar t₀ / (α - 3)) ∧
    IntegrableOn (fun t => t * ‖v t‖ ^ 2) (Set.Ioi t₀) ∧
    ∫ t in Set.Ioi t₀, t * ‖v t‖ ^ 2 ≤ anchoredEnergy Φ x v 2 (2 * (α - 3)) xstar t₀ / (α - 3) := by sorry

end InertialAVD.Traj
