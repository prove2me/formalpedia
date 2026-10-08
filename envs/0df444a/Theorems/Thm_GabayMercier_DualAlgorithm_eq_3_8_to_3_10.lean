-- Prove2me | Theorems.Thm_GabayMercier_DualAlgorithm_eq_3_8_to_3_10
-- name    : GabayMercier.DualAlgorithm.eq_3_8_to_3_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:09:38.431304+00:00
-- url     : https://prove2.me/theorems/70428878-f1ac-494d-8d9c-afffe2cc732c
-- title:
--   (3.8)–(3.10) — a saddle point is a fixed point of Steps 1–2 and y* = Av*
-- statement:
--   Under the standing hypotheses (2.2), (2.3), (2.5), let $(v^*,y^*;\lambda^*)$ be a saddle point of $\mathcal L$ and let $r\in\mathbb R$. Then
--   $$\begin{aligned}
--   &(3.8)\quad r(Av^*,Av)=(ry^*-\lambda^*,Av)+\langle b,v\rangle\quad\forall v\in V,\\
--   &(3.9)\quad (f_1'(y^*),y-y^*)+f_2(y)-f_2(y^*)+(ry^*-\lambda^*-rAv^*,\,y-y^*)\ge0\quad\forall y\in Y,\\
--   &(3.10)\quad y^*=Av^* .
--   \end{aligned}$$
--   Here (3.9) includes $f_2(y^*)<+\infty$ and is stated as $\lambda^*+rAv^*-ry^*-f_1'(y^*)\in\partial f_2(y^*)$.
--
--   So a saddle point is a fixed point of Steps 1 and 2 of the modified dual algorithm; subtracting these relations from the algorithm's is the starting point of the convergence proof.
--
--   **Formalization Note.** The paper derives (3.8)–(3.10) from a saddle point given by Theorem 2.2, where "satisfying (2.8)" is a misprint for (2.10). The paper prints (3.8) with $-\langle b,v\rangle$; with $A'\lambda^*=b$ and $y^*=Av^*$ from (2.10) the correct sign is $+\langle b,v\rangle$, matching Step 1 of the algorithm as defined in this mission. (3.9) uses $\partial f=f_1'+\partial f_2$ (Remark 1, p. 11), valid since $f_1$ is convex and differentiable. The relations hold for every real $r$, in particular for every $r>0$.
-- source:
--   Gabay & Mercier, IRIA RR-126 (1975), hal-04716124v1, p. 16, (3.8)–(3.10)

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_DualAlgorithm_Model

open Filter Topology InertialFB.IFB

namespace GabayMercier.DualAlgorithm

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- (3.8)–(3.10), p. 16: every saddle point `(v*, y*; λ*)` of `ℒ` satisfies, for every `r`,
the fixed-point form of Steps 1–2 of the algorithm, and `y* = Av*`. (3.8) is written with
`+ ⟨b, v⟩`; the paper prints `− ⟨b, v⟩`. -/
theorem eq_3_8_to_3_10 (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₁' : Y → Y) (f₂ : Y → EReal)
    (b : StrongDual ℝ V) (γ α : ℝ) (h : StandingHyp A f₁ f₁' f₂ γ α) (vs : V) (ys ls : Y)
    (hsp : IsSaddlePoint (lagrangian A f₁ f₂ b) vs ys ls) (r : ℝ) :
    (∀ w : V, r * inner ℝ (A vs) (A w) = inner ℝ (r • ys - ls) (A w) + b w) ∧
      IsSubgradient f₂ ys (ls + r • A vs - r • ys - f₁' ys) ∧
      ys = A vs := by sorry

end GabayMercier.DualAlgorithm
