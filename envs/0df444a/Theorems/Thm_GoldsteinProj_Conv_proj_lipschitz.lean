-- Prove2me | Theorems.Thm_GoldsteinProj_Conv_proj_lipschitz
-- name    : GoldsteinProj.Conv.proj_lipschitz
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:23:54.085597+00:00
-- url     : https://prove2.me/theorems/cf7f5442-0716-4117-8272-479028262fc1
-- title:
--   p. 709 — the projection P onto a convex set C is Lipschitzian
-- statement:
--   Let $H$ be a real inner product space, $C \subseteq H$ convex, and $P$ the projection onto $C$ (each $P(x)$ is a closest point of $C$ to $x$). Then $P$ is Lipschitz: there is a constant $K \ge 0$ such that
--   $$\|P(x) - P(x')\| \le K\|x - x'\| \qquad (x, x' \in H).$$
--
--   The continuity of $P$ is what makes the iterates of the gradient projection method depend continuously on the step size, which the convergence proof uses.
--
--   **Formalization Note** The paper does not specify a Lipschitz constant, so the Lean statement quantifies over one.
-- source:
--   Goldstein, Convex programming in Hilbert space, Bull. Amer. Math. Soc. 70 (1964), p. 709, paragraph before the THEOREM

import Mathlib
import Definitions.Def_GoldsteinProj_Conv_Setting

open Filter Topology RealInnerProductSpace

namespace GoldsteinProj.Conv

/-- Goldstein 1964, p. 709: the projection `P` onto a convex set `C` is Lipschitzian. -/
theorem proj_lipschitz {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) (hCv : Convex ℝ C) (P : H → H) (hP : IsProjection C P) :
    ∃ K : NNReal, LipschitzWith K P := by sorry

end GoldsteinProj.Conv
