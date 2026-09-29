-- Prove2me | Theorems.Thm_HeckeEis_IsEichlerIntegral_coeff_binaryFormRepSL_inv_apply_sub_eq_intervalIntegral_slash
-- name    : HeckeEis.IsEichlerIntegral.coeff_binaryFormRepSL_inv_apply_sub_eq_intervalIntegral_slash
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/bcc78cbe-6029-57a6-857b-eeeb2188f4dc
-- title:
--   Period of an Eichler integral around a cusp
-- statement:
--   Fix $n \in \mathbb{N}$. Let $f \colon \mathcal{H} \to \mathbb{C}$ be differentiable as a map of complex manifolds, and let $F \colon \mathcal{H} \to \mathbb{C}[X_0,X_1]_n$ take values in the submodule of polynomials in two variables homogeneous of degree $n$ over $\mathbb{C}$. Assume [`HeckeEis.IsEichlerIntegral n f F`](def/HeckeEis_EichlerIntegral.html#L105), i.e. for every exponent vector $d$ and every $\tau \in \mathcal{H}$ the function $z \mapsto \operatorname{coeff}_d F(z)$ (with $F$ extended to $\mathbb{C}$ by the canonical map onto $\mathcal{H}$) has complex derivative $f(\tau)\cdot\operatorname{coeff}_d\bigl((\tau X_0 + X_1)^n\bigr)$ at $\tau$. Here $\mathrm{SL}_2(\mathbb{Z})$ acts on $\mathbb{C}[X_0,X_1]_n$ by [`HeckeEis.binaryFormRepSL`](def/HeckeEis_BinaryFormRep.html#L61), the substitution $X_j \mapsto \sum_i g_{ij} X_i$. Then for every $\sigma \in \mathrm{SL}_2(\mathbb{Z})$, every $h \in \mathbb{Z}$ and every $\tau \in \mathcal{H}$, writing $u = \sigma T^h \sigma^{-1}$ with $T$ the standard unipotent generator, the coefficient of the monomial $X_1^n$ in $$\rho_n(\sigma^{-1})\bigl(F(u\cdot\tau) - \rho_n(u) F(\tau)\bigr)$$ equals the interval integral $\int_0^h (f \mid_{n+2} \sigma)\bigl(t + \sigma^{-1}\cdot\tau\bigr)\,dt$, taken in the signed sense over the real interval from $0$ to $h$, where $\mid_{n+2}$ is the weight $(n+2)$ slash action and $t$ acts by the horizontal translation $+\!\!\!+_\mathcal{H}$.
--
--   This computes the period of the Eichler–Shimura cocycle $\gamma \mapsto F(\gamma\tau) - \rho_n(\gamma)F(\tau)$ attached to an Eichler integral $F$ of $f$, evaluated on the generator $\sigma T^h \sigma^{-1}$ of the stabiliser of the cusp $\sigma\infty$, as a horocycle integral of $f \mid_{n+2} \sigma$. It is used in the construction comparing coefficient cocycles of modular forms with parabolic cocycles, via [`HeckeEis.exists_modularForm_coeffCocycles_sub_cocycle_mem_coeffParabolicCocycles`](thm.html#HeckeEis.exists_modularForm_coeffCocycles_sub_cocycle_mem_coeffParabolicCocycles).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_IsEichlerIntegral_coeff_binaryFormRepSL_inv_apply_sub_eq_intervalIntegral_slash.lean

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_HeckeEis_EichlerIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem HeckeEis.IsEichlerIntegral.coeff_binaryFormRepSL_inv_apply_sub_eq_intervalIntegral_slash {n : ℕ}
    {f : UpperHalfPlane → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) (σ : SL(2, ℤ)) (h : ℤ) (τ : UpperHalfPlane) :
    MvPolynomial.coeff (Finsupp.single 1 n)
      ((HeckeEis.binaryFormRepSL ℂ n σ⁻¹
          (F ((σ * ModularGroup.T ^ h * σ⁻¹) • τ)
            - HeckeEis.binaryFormRepSL ℂ n (σ * ModularGroup.T ^ h * σ⁻¹) (F τ)) : ↥(HeckeEis.BinaryForm ℂ n)) :
        MvPolynomial (Fin 2) ℂ)
      = ∫ t in (0 : ℝ)..(h : ℝ), (f ∣[((n : ℤ) + 2)] σ) ((t : ℝ) +ᵥ (σ⁻¹ • τ)) := by sorry
