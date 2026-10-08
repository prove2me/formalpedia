-- Prove2me | Theorems.Thm_GabayMercier_Approximation_proposition_2_1
-- name    : GabayMercier.Approximation.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:34.010597+00:00
-- url     : https://prove2.me/theorems/b95e90d5-c0ab-4d40-9b81-6e3d3162a701
-- title:
--   p. 20, after (4.3) — by Proposition 2.1, the quadratic problem (𝒫) has a unique solution
-- statement:
--   Let $V,Y$ be real Hilbert spaces, $A:V\to Y$ continuous linear, and $b\in V'$. Let $f_2:Y\to(-\infty,+\infty]$ be proper, convex and lower semicontinuous, and suppose some $v_0\in V$ has $f_2(Av_0)<+\infty$. If $\alpha>0$ satisfies $\|Av\|^2\ge\alpha^2\|v\|^2$ for every $v\in V$, then
--   $$
--   \exists!v^*\in V:\quad v^*\in\operatorname*{argmin}_{v\in V}\left(\tfrac12\|Av\|^2+f_2(Av)-\langle b,v\rangle\right).
--   $$
--   This is the application of Proposition 2.1 stated on p. 20, after (4.3), in the quadratic case (4.2) ("we verify that the hypothesis (2.3) is satisfied in this case. According to proposition (2.1), there exists a unique solution $v^*$ of $({\cal P})$"), and supplies the target of Theorem 4.1. The general Proposition 2.1 (p. 9, arbitrary $f_1$ under (2.3)) is not restated here.
--
--   **Formalization Note** The paper's proof explicitly assumes a feasible point, saying otherwise the problem has no meaning. This condition is included. The general strong monotonicity assumption (2.3) is automatic for $f_1(y)=\frac12\|y\|^2$.
-- source:
--   Gabay & Mercier, IRIA RR-126 (1975), hal-04716124v1, p. 20, after (4.3) (application of Proposition 2.1, p. 9)

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_Approximation_Model

open Filter Topology InertialFB.IFB

namespace GabayMercier.Approximation

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- p. 20, after (4.3): in the quadratic case (4.2), Proposition 2.1 gives a unique solution of (𝒫). -/
theorem proposition_2_1 (A : V →L[ℝ] Y) (f₂ : Y → EReal) (b : StrongDual ℝ V)
    (hproper : IsProperFn f₂) (hconv : IsConvexFn f₂)
    (hlsc : LowerSemicontinuous f₂) (hfeasible : ∃ v : V, f₂ (A v) ≠ ⊤)
    (α : ℝ) (hα : 0 < α) (hA : ∀ v, α ^ 2 * ‖v‖ ^ 2 ≤ ‖A v‖ ^ 2) :
    ∃! vs : V, GabayMercier.DualAlgorithm.IsSolution A halfSq f₂ b vs := by sorry

end GabayMercier.Approximation
