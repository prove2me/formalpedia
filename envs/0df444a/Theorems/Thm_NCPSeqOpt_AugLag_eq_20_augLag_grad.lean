-- Prove2me | Theorems.Thm_NCPSeqOpt_AugLag_eq_20_augLag_grad
-- name    : NCPSeqOpt.AugLag.eq_20_augLag_grad
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:23:11.782072+00:00
-- url     : https://prove2.me/theorems/61063c59-7dc5-44c4-8d8f-deda29599bd5
-- title:
--   (20), p. 8 — ∇ₓL_ρ(x, Λ) = ∇f(x) + DG(x)*(ρ Π_𝒦°(G(x) + Λ/ρ))
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ and $G:\mathbb R^n\to\mathbb E$ be continuously differentiable, $\mathcal K\subseteq\mathbb E$ a nonempty closed convex cone with polar $\mathcal K^\circ$, $\rho>0$ and $\Lambda\in\mathcal K^\circ$. The augmented Lagrangian
--   $L_\rho(x,\Lambda)=f(x)+\frac\rho2\big[\|\Pi_{\mathcal K^\circ}(G(x)+\Lambda/\rho)\|^2-\|\Lambda/\rho\|^2\big]$
--   is differentiable in $x$ at every $x\in\mathbb R^n$, with
--   $$\nabla_x L_\rho(x,\Lambda)=\nabla f(x)+DG(x)^*\Big(\rho\,\Pi_{\mathcal K^\circ}\Big(G(x)+\frac{\Lambda}{\rho}\Big)\Big). \tag{20}$$
--
--   This formula motivates the multiplier update (22) of Algorithm 1 and turns the stopping test (21) into the approximate stationarity (9).
--
--   **Formalization Note** Stated with `HasGradientAt`, so differentiability is part of the conclusion. $DG(x)^*$ is `ContinuousLinearMap.adjoint (fderiv ℝ G x)`.
-- source:
--   Andreani, Gómez, Haeser, Mito & Ramos, On Optimality Conditions for Nonlinear Conic Programming, author's manuscript (revised 2021-04-20; Math. Oper. Res. doi:10.1287/moor.2021.1203), §4, (20), p. 8

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_NCPSeqOpt_AugLag_Setting

namespace NCPSeqOpt.AugLag

open MoreauProx.Decomposition
open scoped InnerProductSpace
open Filter Topology

theorem eq_20_augLag_grad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (G : EuclideanSpace ℝ (Fin n) → E) (hG : ContDiff ℝ 1 G)
    (K : Set E) (hK : IsClosedConvexCone K)
    (ρ : ℝ) (hρ : 0 < ρ) (Λ : E) (hΛ : Λ ∈ polarCone K) (x : EuclideanSpace ℝ (Fin n)) :
    HasGradientAt (fun y => augLag f G K ρ y Λ)
      (gradient f x + adjD G x (ρ • proj (polarCone K) (G x + ρ⁻¹ • Λ))) x := by sorry

end NCPSeqOpt.AugLag
