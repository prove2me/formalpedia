-- Prove2me | Theorems.Thm_GabayMercier_DualAlgorithm_theorem_3_1
-- name    : GabayMercier.DualAlgorithm.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:13:47.922475+00:00
-- url     : https://prove2.me/theorems/d85aa94e-9dbb-4077-9c27-436e524f0735
-- title:
--   Theorem 3.1 — for 0 < ρ < 2r, the modified dual algorithm converges strongly to (v*, Av*) and λⁿ stays bounded
-- statement:
--   Let $V,Y$ be real Hilbert spaces, $A:V\to Y$ continuous linear, $b\in V'$, and $f=f_1+f_2$ where
--   1. $f_1:Y\to\mathbb R$ is convex and continuously differentiable with strongly monotone gradient: $(f_1'(y)-f_1'(z),y-z)\ge\gamma|y-z|^2$ for some $\gamma>0$ (2.3);
--   2. $f_2:Y\to(-\infty,+\infty]$ is proper, convex and lower semicontinuous;
--   3. $|Av|^2\ge\alpha^2\|v\|^2$ for some $\alpha>0$ (2.5);
--   4. some $Av_0$ lies in the interior of $\operatorname{dom}f_2$ (qualification).
--
--   Let $v^*$ be the solution of $(\mathcal P)$: $\inf_{v\in V}\{f(Av)-\langle b,v\rangle\}$. Let $r>0$ and let the stepsize satisfy
--   $$0<\rho<2r .$$
--   Then every sequence $(v^n,y^n,\lambda^n)_{n\ge0}$ produced by the modified dual algorithm (3.4), from any start $(y^0,\lambda^0)\in Y\times Y$ (Step 1: $r(Av^{n+1},Av)=(ry^n-\lambda^n,Av)+\langle b,v\rangle$ for all $v$; Step 2: $\lambda^n+rAv^{n+1}-ry^{n+1}-f_1'(y^{n+1})\in\partial f_2(y^{n+1})$; Step 3: $\lambda^{n+1}=\lambda^n+\rho(Av^{n+1}-y^{n+1})$), satisfies
--   $$\|v^n-v^*\|\to0,\qquad |y^n-Av^*|\to0,$$
--   and the multipliers $(\lambda^n)$ stay bounded in $Y$.
--
--   This is the convergence theorem for the alternating direction method of multipliers in Hilbert space, for any stepsize below twice the penalty parameter. The solution $v^*$ exists and is unique (Proposition 2.1), so the hypothesis on $v^*$ can be met; the multipliers need not converge because the multiplier $\lambda^*$ need not be unique.
--
--   **Formalization Note.** Strong convergence in $V\times Y$ is stated as the two norm limits. $v^*$ enters through the hypothesis `IsSolution` (finite value and minimal). The statement quantifies over every run of the algorithm; the algorithm's well-posedness (Remark 1, p. 15) is not used. Two departures from the printed text, both explained in the definition file: Step 1 carries $+\langle b,v\rangle$ (the paper prints $-\langle b,v\rangle$, which makes the algorithm solve (𝒫) with $-b$; for $V=Y=\mathbb R$, $A=\mathrm{id}$, $f_1(y)=y^2/2$, $f_2=0$, $\langle b,v\rangle=v$ the printed iteration converges to $-1$ while $v^*=1$); and the paper's qualification (2.4), $\operatorname{int}\operatorname{dom}f_2\ne\emptyset$, is strengthened to $\operatorname{int}\operatorname{dom}f_2\cap R(A)\ne\emptyset$. Under (2.4) alone the multipliers can be unbounded: in the example of Theorem 2.1 (converse) ($V=\mathbb R$, $Y=\mathbb R^2$, $Av=(v,0)$, $f_2$ the indicator of the disc of centre $(0,1)$ and radius $1$, $\langle b,v\rangle=v$), no saddle point exists, and the conclusion of Theorem 3.1 fails for $r=\rho=1$: if $v^n\to0$ and $y^n\to0$, a bounded $(\lambda^n)$ would have a weak cluster point $\bar\lambda$ with $\bar\lambda_1=1$ by Step 1 and $\bar\lambda\in\partial f_2(0)$ by Step 2, which forces $\bar\lambda_1=0$ (numerically, $\lambda^n_2\approx-113$ after $10^6$ iterations and still decreasing).
-- source:
--   Gabay & Mercier, IRIA RR-126 (1975), hal-04716124v1, p. 19, Theorem 3.1

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_DualAlgorithm_Model

open Filter Topology InertialFB.IFB

namespace GabayMercier.DualAlgorithm

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- Theorem 3.1, p. 19: for every stepsize `0 < ρ < 2r`, every run of the modified dual algorithm
(3.4) converges strongly in `V × Y` to `(v*, Av*)`, where `v*` is the solution of (𝒫), and the
multipliers `λⁿ` stay bounded. The qualification hypothesis strengthens the paper's (2.4). -/
theorem theorem_3_1 (A : V →L[ℝ] Y) (f₁ : Y → ℝ) (f₁' : Y → Y) (f₂ : Y → EReal)
    (b : StrongDual ℝ V) (γ α : ℝ) (h : StandingHyp A f₁ f₁' f₂ γ α)
    (hq : Qualification A f₂) (r ρ : ℝ) (hr : 0 < r) (hρ : 0 < ρ) (hρr : ρ < 2 * r)
    (v : ℕ → V) (y lam : ℕ → Y) (hrun : IsModifiedDualRun A f₁' f₂ b r ρ v y lam)
    (vs : V) (hvs : IsSolution A f₁ f₂ b vs) :
    Tendsto v atTop (𝓝 vs) ∧ Tendsto y atTop (𝓝 (A vs)) ∧
      Bornology.IsBounded (Set.range lam) := by sorry

end GabayMercier.DualAlgorithm
