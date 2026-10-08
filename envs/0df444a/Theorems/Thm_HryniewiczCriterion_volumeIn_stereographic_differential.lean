-- Prove2me | Theorems.Thm_HryniewiczCriterion_volumeIn_stereographic_differential
-- name    : HryniewiczCriterion.volumeIn_stereographic_differential
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-08T02:30:12.316967+00:00
-- url     : https://prove2.me/theorems/0d2e7502-fd8f-4ef7-ba3e-615eb8dce81d
-- title:
--   Stereographic projection $S^3\setminus\{N\}\to N^\perp$ preserves orientation: Jacobian formula
-- statement:
--   Let $N,y\in S^3\subset\mathbb{R}^4$ with $y\neq N$, and put $k=\langle y,N\rangle$, so $k<1$. The differential of the stereographic projection $\sigma_N(y)=\dfrac{y-\langle y,N\rangle N}{1-\langle y,N\rangle}$ (`stereographicFrom`) at $y$ is
--   $$d\sigma_y(x)=\frac{x-\langle x,N\rangle N}{1-k}+\frac{\langle x,N\rangle}{(1-k)^2}\,(y-kN).$$
--   For tangent vectors $x_1,x_2,x_3\perp y$,
--   $$\det\big(-N,\ d\sigma_y x_1,\ d\sigma_y x_2,\ d\sigma_y x_3\big)=\frac{\det(y,x_1,x_2,x_3)}{(1-k)^3},$$
--   where the left side is `volumeIn N` (the volume form of $N^\perp$ oriented by $\det(-N,\cdot,\cdot,\cdot)$). Since $1-k>0$, stereographic projection is orientation preserving from $S^3$, oriented as the boundary of the unit ball, to $N^\perp$.
--
--   Proof: the $N$-components drop out, and multilinearity leaves $(1-k)^{-3}\det(-N,x_1,x_2,x_3)+(1-k)^{-4}\sum_i\langle x_i,N\rangle\det(-N,\dots,y,\dots)$. Two instances of the five-vector Laplace (Cramer) identity, paired with $y$ and with $N$, give $\det(N,x_1,x_2,x_3)=kD$ and $\sum_i\langle x_i,N\rangle\det(y,\dots,N,\dots)=(1-k^2)D$, where $D=\det(y,x_1,x_2,x_3)$. The total is $(1-k)^{-3}(-kD+(1+k)D)=D/(1-k)^3$.
-- source:
--   Standard (stereographic projection is a conformal orientation-preserving diffeomorphism S^3 \ {N} -> R^3); used for the orientation conventions of the Gauss linking integral in U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Definition 1.5.

import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.volumeIn_stereographic_differential (N y x₁ x₂ x₃ : R4) (hN : euclidNorm N = 1) (hy : euclidNorm y = 1) (hyN : y ≠ N)
    (h₁ : dot4 x₁ y = 0) (h₂ : dot4 x₂ y = 0) (h₃ : dot4 x₃ y = 0) :
    volumeIn N ((1 - dot4 y N)⁻¹ • (x₁ - dot4 x₁ N • N) + (dot4 x₁ N / (1 - dot4 y N) ^ 2) • (y - dot4 y N • N))
      ((1 - dot4 y N)⁻¹ • (x₂ - dot4 x₂ N • N) + (dot4 x₂ N / (1 - dot4 y N) ^ 2) • (y - dot4 y N • N))
      ((1 - dot4 y N)⁻¹ • (x₃ - dot4 x₃ N • N) + (dot4 x₃ N / (1 - dot4 y N) ^ 2) • (y - dot4 y N • N)) =
      Matrix.det (Matrix.of ![y, x₁, x₂, x₃]) / (1 - dot4 y N) ^ 3 := by sorry
