-- Prove2me | Theorems.Thm_HeckeEis_jFactor_pow_mul_eval_binaryFormRepSL
-- name    : HeckeEis.jFactor_pow_mul_eval_binaryFormRepSL
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/494216ec-849a-5e02-bbdf-6d4fb405713d
-- title:
--   Weight identity j(g,τ)ⁿ(ρₙ(g)P)(1,-gτ)=P(1,-τ)
-- statement:
--   Fix a natural number $n$, an element $g\in\mathrm{SL}_2(\mathbb{Z})$, a point $\tau$ of the upper half-plane, and an element $P$ of [`HeckeEis.BinaryForm ℂ n`](def/HeckeEis_BinaryFormRep.html#L25), that is, of the submodule of $\mathbb{C}[X_0,X_1]$ (polynomials in two variables indexed by `Fin 2`) consisting of the forms homogeneous of degree $n$. Here [`HeckeEis.jFactor g τ`](def/HeckeEis_EichlerIntegral.html#L28) denotes the complex number $g_{10}\tau+g_{11}$ formed from the bottom row of the integer matrix underlying $g$, and [`HeckeEis.binaryFormRepSL ℂ n`](def/HeckeEis_BinaryFormRep.html#L61) is the representation of $\mathrm{SL}_2(\mathbb{Z})$ on degree-$n$ binary forms obtained by restricting to that submodule the algebra endomorphism of $\mathbb{C}[X_0,X_1]$ that substitutes $X_j\mapsto\sum_{i}g_{ij}X_i$, i.e. substitution of the row vector times the matrix $g$. The assertion is the identity of complex numbers
--   $$\big(g_{10}\tau+g_{11}\big)^{n}\cdot\big(\rho_n(g)P\big)\big(1,\,-(g\cdot\tau)\big)=P\big(1,\,-\tau\big),$$
--   where both sides are evaluations of the underlying polynomials at the indicated points of $\mathbb{C}^2$ (given as `Fin 2`-vectors), $\rho_n(g)P$ is the image of $P$ under the above representation, and $g\cdot\tau$ is the Möbius action of $g$ on the upper half-plane.
--
--   This is the compatibility between the degree-$n$ substitution action on binary forms and the line spanned by $(1,-\tau)$: pairing a $\rho_n$-equivariant vector-valued function with $(1,-\tau)$ produces a scalar function transforming with weight $-n$, which is the mechanism behind the Eichler–Shimura period map. It is used in the proof that the Eichler–Shimura map is injective ([`HeckeEis.eichlerShimuraMap_injective`](thm.html#HeckeEis.eichlerShimuraMap_injective)) and in the boundedness of such evaluations towards the cusp $i\infty$ ([`HeckeEis.IsEichlerIntegral.isBoundedAtImInfty_eval`](thm.html#HeckeEis.IsEichlerIntegral.isBoundedAtImInfty_eval)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_jFactor_pow_mul_eval_binaryFormRepSL.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem HeckeEis.jFactor_pow_mul_eval_binaryFormRepSL (n : ℕ) (g : SL(2, ℤ)) (τ : UpperHalfPlane)
    (P : ↥(HeckeEis.BinaryForm ℂ n)) :
    HeckeEis.jFactor g τ ^ n * MvPolynomial.eval ![(1 : ℂ), -(((g • τ : UpperHalfPlane)) : ℂ)]
        ((HeckeEis.binaryFormRepSL ℂ n g P : ↥(HeckeEis.BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)
      = MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] (P : MvPolynomial (Fin 2) ℂ) := by sorry
