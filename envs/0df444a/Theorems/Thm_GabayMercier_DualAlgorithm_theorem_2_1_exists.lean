-- Prove2me | Theorems.Thm_GabayMercier_DualAlgorithm_theorem_2_1_exists
-- name    : GabayMercier.DualAlgorithm.theorem_2_1_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:09:28.650511+00:00
-- url     : https://prove2.me/theorems/c003105b-352f-43f1-821b-01ff1c343044
-- title:
--   Theorem 2.1 (converse) — under (2.3), (2.5) and A v₀ ∈ int dom f₂, ℒ has a saddle point
-- statement:
--   Under the standing hypotheses (2.2), (2.3), (2.5), assume the qualification hypothesis
--   $$\exists v_0\in V:\qquad Av_0\in\operatorname{int}\operatorname{dom}f_2 .$$
--   Then the Lagrangian $\mathcal L(v,y;\lambda)=f(y)+(\lambda,Av-y)-\langle b,v\rangle$ has at least one saddle point $(v^*,y^*;\lambda^*)\in(V\times Y)\times Y$.
--
--   By the first part of Theorem 2.1, such a saddle point consists of the solution $v^*$ of (𝒫), $y^*=Av^*$ and a Lagrange multiplier $\lambda^*\in\partial f(Av^*)$ with $A'\lambda^*=b$. The existence of this multiplier is what the convergence analysis of Section 3 is built on.
--
--   **Formalization Note.** The paper states the converse under (2.3), (2.4), (2.5), where (2.4) is "the interior in $Y$ of $\operatorname{dom}f_2$ is non empty". Its proof applies the chain rule $\partial(f\circ A)(v)=A'\partial f(Av)$ ([E] ch. 1, PR 5.7), which needs $f$ finite and continuous at a point of the range of $A$; Remark 2 (p. 11) states this stronger hypothesis for the general case. With (2.4) alone the statement is false: take $V=\mathbb R$, $Y=\mathbb R^2$, $Av=(v,0)$, $f_1(y)=|y|^2/2$, $f_2$ the indicator of the closed disc of centre $(0,1)$ and radius $1$, and $\langle b,v\rangle=v$. All of (2.2)–(2.5) hold, $v^*=0$, but $\partial f(0)=\{(0,-t):t\ge0\}$ contains no $\lambda$ with $A'\lambda=\lambda_1=1$. We therefore state the theorem under $Av_0\in\operatorname{int}\operatorname{dom}f_2$, which implies (2.4).
-- source:
--   Gabay & Mercier, IRIA RR-126 (1975), hal-04716124v1, p. 9, Theorem 2.1 (converse); proof pp. 10–11

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_DualAlgorithm_Model

open Filter Topology InertialFB.IFB

namespace GabayMercier.DualAlgorithm

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- Theorem 2.1, p. 9, converse: under (2.3), (2.5) and the qualification hypothesis
(`A v₀ ∈ int dom f₂` for some `v₀`, strengthening (2.4)), `ℒ` has a saddle point. -/
theorem theorem_2_1_exists (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₁' : Y → Y) (f₂ : Y → EReal)
    (b : StrongDual ℝ V) (γ α : ℝ) (h : StandingHyp A f₁ f₁' f₂ γ α)
    (hq : Qualification A f₂) :
    ∃ (vs : V) (ys ls : Y), IsSaddlePoint (lagrangian A f₁ f₂ b) vs ys ls := by sorry

end GabayMercier.DualAlgorithm
