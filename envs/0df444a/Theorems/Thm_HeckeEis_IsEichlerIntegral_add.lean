-- Prove2me | Theorems.Thm_HeckeEis_IsEichlerIntegral_add
-- name    : HeckeEis.IsEichlerIntegral.add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/c1c5c079-2722-5cb7-92f5-1c48ef405037
-- title:
--   Additivity of the Eichler integral relation
-- statement:
--   Let $n$ be a natural number, let $f,g:\mathcal H\to\mathbb C$ be functions on the upper half-plane, and let $F,G:\mathcal H\to \mathrm{BinaryForm}\,\mathbb C\,n$ be functions with values in the submodule of $\mathbb C[X_0,X_1]$ of polynomials homogeneous of degree $n$ ([`HeckeEis.BinaryForm ℂ n`](def/HeckeEis_BinaryFormRep.html#L25) is `MvPolynomial.homogeneousSubmodule (Fin 2) ℂ n`). The hypotheses are that $F$ is an Eichler integral of $f$ in the sense of [`HeckeEis.IsEichlerIntegral`](def/HeckeEis_EichlerIntegral.html#L105), i.e. for every multidegree $d:\mathrm{Fin}\,2\to_0\mathbb N$ and every $\tau\in\mathcal H$ the function $z\mapsto \mathrm{coeff}_d\big(F(\mathrm{ofComplex}\,z)\big)$ of a complex variable has derivative $f(\tau)\cdot \mathrm{coeff}_d\big((\tau X_0+X_1)^n\big)$ at the point $z=\tau$, and that $G$ stands in the same relation to $g$. The conclusion is that the pointwise sum $F+G$ is an Eichler integral of $f+g$ in exactly the same sense: for all $d$ and $\tau$, the coefficient function of $F+G$ in degree $d$ is differentiable at $\tau$ with derivative $(f+g)(\tau)\cdot \mathrm{coeff}_d\big((\tau X_0+X_1)^n\big)$. No holomorphy, growth or modularity assumption on $f$, $g$, $F$ or $G$ enters.
--
--   This is the additivity half of the bilinearity of the Eichler integral relation $dF=f(\tau)(\tau X_0+X_1)^n\,d\tau$ between a weight $n+2$ form and its $\mathrm{Sym}^n$-valued primitive. It is used to prove that the Eichler–Shimura map is additive ([`HeckeEis.eichlerShimuraMap_add`](thm.html#HeckeEis.eichlerShimuraMap_add)), and more generally whenever Eichler integrals of sums of translates occur.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_IsEichlerIntegral_add.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem HeckeEis.IsEichlerIntegral.add {n : ℕ} {f g : UpperHalfPlane → ℂ} {F G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) (hG : HeckeEis.IsEichlerIntegral n g G) :
    HeckeEis.IsEichlerIntegral n (f + g) (F + G) := by sorry
