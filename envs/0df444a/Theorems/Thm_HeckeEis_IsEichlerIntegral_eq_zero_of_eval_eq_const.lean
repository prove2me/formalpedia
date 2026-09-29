-- Prove2me | Theorems.Thm_HeckeEis_IsEichlerIntegral_eq_zero_of_eval_eq_const
-- name    : HeckeEis.IsEichlerIntegral.eq_zero_of_eval_eq_const
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/fe5d2f3a-0740-57ed-8313-443b017b4ca1
-- title:
--   Eichler integral with constant evaluation at (1,-τ) integrates zero
-- statement:
--   Fix a natural number $n$, a function $g\colon\mathfrak H\to\mathbb C$ on the upper half-plane, and a function $G$ on $\mathfrak H$ with values in [`HeckeEis.BinaryForm ℂ n`](def/HeckeEis_BinaryFormRep.html#L25), the submodule of $\mathbb C$-coefficient polynomials in two variables $X_0,X_1$ that are homogeneous of degree $n$. Assume $G$ is an Eichler integral of $g$ in the sense of [`HeckeEis.IsEichlerIntegral`](def/HeckeEis_EichlerIntegral.html#L105): for every multi-exponent $d\in(\mathrm{Fin}\,2\to_0\mathbb N)$ and every $\tau\in\mathfrak H$, the function $z\mapsto$ (coefficient of $d$ in $G(\mathrm{ofComplex}\,z)$), defined on $\mathbb C$ via the retraction $\mathrm{ofComplex}$ onto the upper half-plane, is differentiable at $\tau$ with derivative $g(\tau)$ times the coefficient of $d$ in $(\tau X_0+X_1)^n$; thus coefficientwise $G'(\tau)=g(\tau)\,(\tau X_0+X_1)^n$. Assume further that there is a constant $c\in\mathbb C$ such that for every $\tau\in\mathfrak H$ the binary form $G(\tau)$ evaluated at $(X_0,X_1)=(1,-\tau)$, the zero of $\tau X_0+X_1$, equals $c$. The conclusion is that $g$ is the zero function on $\mathfrak H$.
--
--   This is the uniqueness statement underlying the Eichler–Shimura correspondence: evaluation of an Eichler integral of weight $n+2$ at the moving point $(1,-\tau)$ determines the integrated function up to nothing, so a constant period function forces the form to vanish. It is used for the injectivity of the Eichler–Shimura map, via [`HeckeEis.eichlerShimuraMap_injective`](thm.html#HeckeEis.eichlerShimuraMap_injective) and [`HeckeEis.modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero`](thm.html#HeckeEis.modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_IsEichlerIntegral_eq_zero_of_eval_eq_const.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem HeckeEis.IsEichlerIntegral.eq_zero_of_eval_eq_const {n : ℕ} {g : UpperHalfPlane → ℂ}
    {G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)} (hG : HeckeEis.IsEichlerIntegral n g G) {c : ℂ}
    (hc : ∀ τ : UpperHalfPlane,
      MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] ((G τ : ↥(HeckeEis.BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ) = c) :
    g = 0 := by sorry
