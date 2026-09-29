-- Prove2me | Theorems.Thm_HeckeEis_IsEichlerIntegral_isBoundedAtImInfty_eval
-- name    : HeckeEis.IsEichlerIntegral.isBoundedAtImInfty_eval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/4344e0ba-9030-543a-8d2f-88300d4dc110
-- title:
--   Boundedness at i∞ of a T^h-equivariant Eichler integral's evaluation
-- statement:
--   Fix $n\in\mathbb N$, a function $g:\mathfrak H\to\mathbb C$ on the upper half-plane, and a function $G$ from $\mathfrak H$ to [`HeckeEis.BinaryForm ℂ n`](def/HeckeEis_BinaryFormRep.html#L25), the submodule of degree-$n$ homogeneous elements of $\mathbb C[X_0,X_1]$. The hypothesis [`HeckeEis.IsEichlerIntegral n g G`](def/HeckeEis_EichlerIntegral.html#L105) says that $G$ is an Eichler integral of $g$ coefficientwise: for every multidegree $d$ and every $\tau\in\mathfrak H$, the function $z\mapsto \mathrm{coeff}_d\bigl(G(\mathrm{ofComplex}\,z)\bigr)$ on $\mathbb C$ has derivative at $\tau$ equal to $g(\tau)\cdot\mathrm{coeff}_d\bigl((\tau X_0+X_1)^n\bigr)$. Assume further an integer $h>0$ such that $g\circ\mathrm{ofComplex}$ is periodic with period $h$; that $g$ is differentiable as a map of complex manifolds $\mathfrak H\to\mathbb C$; that $g$ is bounded at $i\infty$ (`UpperHalfPlane.IsBoundedAtImInfty`); and that $G$ is exactly $T^h$-equivariant, i.e. $G(h+\tau)=\rho_n(T^h)\,G(\tau)$ for all $\tau$, where $\rho_n=$ [`HeckeEis.binaryFormRepSL ℂ n`](def/HeckeEis_BinaryFormRep.html#L61) is the representation of $\mathrm{SL}_2(\mathbb Z)$ on binary forms obtained by substituting $X_j\mapsto\sum_i M_{ij}X_i$, and $T=\begin{pmatrix}1&1\\0&1\end{pmatrix}$. The conclusion is that the scalar function $\tau\mapsto G(\tau)(1,-\tau)$, the evaluation of the binary form $G(\tau)$ at $(X_0,X_1)=(1,-\tau)$, is bounded at $i\infty$.
--
--   This is the cuspidal growth estimate in the Eichler–Shimura argument: exact equivariance under the stabiliser generator $T^h$ forces the polynomial part of an Eichler integral at the cusp to contribute only a constant after evaluation at $(1,-\tau)$. It feeds the injectivity of the Eichler–Shimura map, [`HeckeEis.eichlerShimuraMap_injective`](thm.html#HeckeEis.eichlerShimuraMap_injective), and the vanishing statement [`HeckeEis.modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero`](thm.html#HeckeEis.modularForm_eq_zero_of_coeffH1Mk_cocycle_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_IsEichlerIntegral_isBoundedAtImInfty_eval.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem HeckeEis.IsEichlerIntegral.isBoundedAtImInfty_eval {n : ℕ} {g : UpperHalfPlane → ℂ}
    {G : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)} (hG : HeckeEis.IsEichlerIntegral n g G) {h : ℤ} (hh : 0 < h)
    (hper : Function.Periodic (g ∘ UpperHalfPlane.ofComplex) ((h : ℝ) : ℂ))
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g) (hbdd : UpperHalfPlane.IsBoundedAtImInfty g)
    (hT : ∀ τ : UpperHalfPlane, G ((h : ℝ) +ᵥ τ) = HeckeEis.binaryFormRepSL ℂ n (ModularGroup.T ^ h) (G τ)) :
    UpperHalfPlane.IsBoundedAtImInfty (fun τ : UpperHalfPlane =>
      MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] ((G τ : ↥(HeckeEis.BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)) := by sorry
