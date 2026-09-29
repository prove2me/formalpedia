-- Prove2me | Theorems.Thm_ModularCurve_SiegelUnit_differentiableOn_siegelFun
-- name    : ModularCurve.SiegelUnit.differentiableOn_siegelFun
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/1fec2abc-8e66-5ced-a219-4490663fe4e3
-- title:
--   Holomorphy of the Siegel function g_{r,s} on H
-- statement:
--   Let $N$ be a natural number and $r,s$ integers, with no hypothesis that $N$ be nonzero or that $(r,s)$ be reduced modulo $N$. Write $q = \exp(2\pi i z)$ and $q_a = \exp(2\pi i (rz+s)/N)$, and let `siegelFun` be the function of $z \in \mathbb{C}$ given by the product of the constant $-\exp\bigl(\pi i\, s(r-N)/N^{2}\bigr)$, the exponential $\exp\bigl(\pi i\,((r/N)^{2} - r/N + 1/6)\,z\bigr)$, the factor $1 - q_a$, and the unconditional infinite product $\prod'_{n \in \mathbb{N}} (1 - q^{\,n+1} q_a)(1 - q^{\,n+1} q_a^{-1})$ (Mathlib's `tprod`, which takes the value $1$ when the family is not multipliable). The theorem asserts the conjunction of two differentiability statements for this function: first, that $z \mapsto \mathrm{siegelFun}\,N\,r\,s\,z$ is $\mathbb{C}$-differentiable on the open set $\{z \in \mathbb{C} \mid \operatorname{Im} z > 0\}$; second, that the composite of the coercion $\mathbb{H} \hookrightarrow \mathbb{C}$ with this function is differentiable in the manifold sense, for the model with corners $\mathcal{I}(\mathbb{C})$ on source and target, as a map on the upper half-plane $\mathbb{H}$. Nothing is claimed about behaviour at the cusps, nor about non-vanishing.
--
--   This records the holomorphy, on the open upper half-plane, of the Siegel function of level $N$ and index $(r,s)$ in its $q$-product form, in both the plain complex-analytic and the manifold formulations; the convergence of the product is obtained from the theta-product identity [`jacobiTheta_two_eq_tprod`](thm.html#jacobiTheta_two_eq_tprod). It feeds the construction of a modular form on $\Gamma_1(N)$ as a product of powers of Siegel functions times a power of the modular discriminant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SiegelUnit_differentiableOn_siegelFun.lean

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open scoped Manifold in

theorem ModularCurve.SiegelUnit.differentiableOn_siegelFun (N : ℕ) (r s : ℤ) :
    DifferentiableOn ℂ (fun z : ℂ => siegelFun N r s z) {z : ℂ | 0 < z.im} ∧
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : UpperHalfPlane => siegelFun N r s (τ : ℂ)) := by sorry
