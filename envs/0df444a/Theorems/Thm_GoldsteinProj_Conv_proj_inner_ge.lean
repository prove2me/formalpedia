-- Prove2me | Theorems.Thm_GoldsteinProj_Conv_proj_inner_ge
-- name    : GoldsteinProj.Conv.proj_inner_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:23:34.361585+00:00
-- url     : https://prove2.me/theorems/d66d9b6c-f3d6-4293-90e2-0605cd38b985
-- title:
--   p. 709 — projection inequality [x − y, P(x) − y] ≧ ‖P(x) − y‖² for x ∈ H, y ∈ C
-- statement:
--   Let $H$ be a real inner product space with inner product $[\cdot,\cdot]$, let $C \subseteq H$ be convex, and let $P$ be the projection onto $C$ (each $P(x)$ is a closest point of $C$ to $x$). Then for every $x \in H$ and every $y \in C$,
--   $$[x - y,\; P(x) - y] \;\ge\; \|P(x) - y\|^2.$$
--
--   This is the basic inequality of the metric projection; it expresses that $C$ lies on one side of the hyperplane through $P(x)$ with normal $x - P(x)$. Every descent estimate of the gradient projection method starts from it.
--
--   **Formalization Note** Closedness of $C$ and completeness of $H$ are not needed once $P$ is given, so they are not assumed.
-- source:
--   Goldstein, Convex programming in Hilbert space, Bull. Amer. Math. Soc. 70 (1964), p. 709, paragraph before the THEOREM

import Mathlib
import Definitions.Def_GoldsteinProj_Conv_Setting

open Filter Topology RealInnerProductSpace

namespace GoldsteinProj.Conv

/-- Goldstein 1964, p. 709: for the projection `P` onto a convex set `C`, every `x ∈ H` and `y ∈ C`
satisfy `⟪x - y, P x - y⟫ ≥ ‖P x - y‖²`. -/
theorem proj_inner_ge {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) (hCv : Convex ℝ C) (P : H → H) (hP : IsProjection C P) :
    ∀ x : H, ∀ y ∈ C, ‖P x - y‖ ^ 2 ≤ ⟪x - y, P x - y⟫ := by sorry

end GoldsteinProj.Conv
