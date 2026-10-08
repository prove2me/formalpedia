-- Prove2me | Theorems.Thm_GabayMercier_DualAlgorithm_theorem_2_2
-- name    : GabayMercier.DualAlgorithm.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:09:54.581824+00:00
-- url     : https://prove2.me/theorems/04aebdc8-d2f4-48b1-967b-dca12c7b965f
-- title:
--   Theorem 2.2 — for r > 0, ℒ_r and ℒ have the same saddle points
-- statement:
--   Let $f_1:Y\to\mathbb R$ be convex and $f_2:Y\to(-\infty,+\infty]$ proper and convex, and let $r>0$. For a triple $(v^*,y^*;\lambda^*)\in(V\times Y)\times Y$, the following are equivalent:
--   1. $(v^*,y^*;\lambda^*)$ is a saddle point of the augmented Lagrangian
--   $$\mathcal L_r(v,y;\lambda)=f(y)+(\lambda,Av-y)+\frac r2|Av-y|^2-\langle b,v\rangle ;$$
--   2. $(v^*,y^*;\lambda^*)$ is a saddle point of the Lagrangian $\mathcal L(v,y;\lambda)=f(y)+(\lambda,Av-y)-\langle b,v\rangle$.
--
--   The augmented term changes the inner minimization (it makes it coercive and uniquely solvable) without changing the saddle points, which is why the algorithm of Section 3, built on $\mathcal L_r$, targets the saddle points of $\mathcal L$.
--
--   **Formalization Note.** The paper states the theorem with only "$r>0$"; its proof (2.22) uses the convexity of $f$, a standing hypothesis (2.2), and properness of $f_2$ (p. 9). Both are stated explicitly; the forward direction fails without convexity. The parenthesised corollary that follows the theorem on p. 12 ("Hence, if (2.3), (2.4), (2.5) hold, … there exists a saddle point of $\mathcal L_r$") is not part of this statement.
-- source:
--   Gabay & Mercier, IRIA RR-126 (1975), hal-04716124v1, p. 12, Theorem 2.2

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_DualAlgorithm_Model

open Filter Topology InertialFB.IFB

namespace GabayMercier.DualAlgorithm

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- Theorem 2.2, p. 12: for `r > 0` (and `f₁`, `f₂` convex, `f₂` proper, as in (2.2)), the saddle
points of the augmented Lagrangian `ℒ_r` are exactly the saddle points of `ℒ`. -/
theorem theorem_2_2 (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₂ : Y → EReal) (b : StrongDual ℝ V)
    (hf₁ : ConvexOn ℝ Set.univ f₁) (hf₂c : IsConvexFn f₂) (hf₂p : IsProperFn f₂)
    (r : ℝ) (hr : 0 < r) (vs : V) (ys ls : Y) :
    IsSaddlePoint (augLagrangian A f₁ f₂ b r) vs ys ls ↔
      IsSaddlePoint (lagrangian A f₁ f₂ b) vs ys ls := by sorry

end GabayMercier.DualAlgorithm
