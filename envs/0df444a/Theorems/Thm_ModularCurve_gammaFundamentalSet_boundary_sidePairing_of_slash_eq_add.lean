-- Prove2me | Theorems.Thm_ModularCurve_gammaFundamentalSet_boundary_sidePairing_of_slash_eq_add
-- name    : ModularCurve.gammaFundamentalSet_boundary_sidePairing_of_slash_eq_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/16fe51ac-3e7c-534d-becf-3576fba25b56
-- title:
--   Side pairing on the boundary of a tiled fundamental set
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$ of finite index, and for each coset $q \in \mathrm{SL}_2(\mathbb{Z})/\Gamma$ write $R_q :=$ `Quotient.out q` for the chosen representative. Let $\varphi, \psi : \mathbb{H} \to \mathbb{C}$ and $c : \mathrm{SL}_2(\mathbb{Z}) \to \mathbb{C}$ satisfy the twisted weight-two transformation law $\varphi(\gamma\tau)/\mathrm{denom}(\gamma,\tau)^2 = \varphi(\tau) + c(\gamma)\,\psi(\tau)$ for all $\gamma \in \Gamma$ and $\tau \in \mathbb{H}$, where $\mathrm{denom}$ is taken for the image of $\gamma$ in $\mathrm{GL}_2(\mathbb{R})$. Let $\Phi, \Psi : \mathrm{SL}_2(\mathbb{Z}) \to \mathbb{C} \to \mathbb{C}$ be given by $\Phi_\sigma(z) = \varphi(\sigma \cdot \mathrm{ofComplex}\,z)/\mathrm{denom}(\sigma, \mathrm{ofComplex}\,z)^2$ and the same formula for $\Psi$ with $\psi$. Let $s \subseteq (0,\infty)$ be measurable, assume that for every $q$ the functions $y \mapsto \Phi_{R_q^{-1}}(-\tfrac12 + iy)$ and $y \mapsto \Psi_{R_q^{-1}}(-\tfrac12 + iy)$ are integrable on $s$, and that $\theta \mapsto \Phi_{R_q^{-1}}(e^{i\theta})\, i e^{i\theta}$ and $\theta \mapsto \Psi_{R_q^{-1}}(e^{i\theta})\, i e^{i\theta}$ are interval-integrable on $[\pi/3, 2\pi/3]$. Then two identities hold simultaneously: first, $\sum_q \int_s \Phi_{R_q^{-1}}(\tfrac12 + iy)\,dy = \sum_q \int_s \Phi_{R_q^{-1}}(-\tfrac12 + iy)\,dy + \sum_q c(R_{Tq}^{-1} T R_q) \int_s \Psi_{R_q^{-1}}(-\tfrac12 + iy)\,dy$, with $T =$ `ModularGroup.T` acting on the coset space; second, $2\sum_q \int_{\pi/3}^{2\pi/3} \Phi_{R_q^{-1}}(e^{i\theta})\, i e^{i\theta}\,d\theta = -\sum_q c(R_{Sq}^{-1} S R_q) \int_{\pi/3}^{2\pi/3} \Psi_{R_q^{-1}}(e^{i\theta})\, i e^{i\theta}\,d\theta$, with $S =$ `ModularGroup.S`.
--
--   This is the side-pairing, or unfolding, step for contour integration over the fundamental polygon of $\Gamma$ tiled by the translates $R_q^{-1}\mathcal{D}$ of the standard fundamental domain of $\mathrm{SL}_2(\mathbb{Z})$: the vertical edges are paired by $T$ and the two halves of the unit-circle arc by $S$, so that the corresponding boundary integrals cancel up to the twist $c$ evaluated at the side-pairing elements $R_{gq}^{-1} g R_q \in \Gamma$. It is used in the boundary evaluations behind the Eichler–Shimura and Petersson pairing computations for the fundamental set of $\Gamma$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_gammaFundamentalSet_boundary_sidePairing_of_slash_eq_add.lean

import Mathlib
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups

theorem ModularCurve.gammaFundamentalSet_boundary_sidePairing_of_slash_eq_add
    (Γ : Subgroup SL(2, ℤ)) [Fintype (SL(2, ℤ) ⧸ Γ)]
    (φ ψ : ℍ → ℂ) (c : SL(2, ℤ) → ℂ)
    (hφ : ∀ γ ∈ Γ, ∀ τ : ℍ,
      φ (γ • τ) / denom (γ : GL (Fin 2) ℝ) τ ^ 2 = φ τ + c γ * ψ τ)
    (Φ Ψ : SL(2, ℤ) → ℂ → ℂ)
    (hΦ : ∀ (σ : SL(2, ℤ)) (z : ℂ),
      Φ σ z = φ (σ • ofComplex z) / denom (σ : GL (Fin 2) ℝ) (ofComplex z) ^ 2)
    (hΨ : ∀ (σ : SL(2, ℤ)) (z : ℂ),
      Ψ σ z = ψ (σ • ofComplex z) / denom (σ : GL (Fin 2) ℝ) (ofComplex z) ^ 2)
    (s : Set ℝ) (hs : MeasurableSet s) (hs0 : s ⊆ Set.Ioi 0)
    (hΦs : ∀ q : SL(2, ℤ) ⧸ Γ,
      IntegrableOn (fun y : ℝ => Φ (Quotient.out q)⁻¹ (-(1 / 2) + y * Complex.I)) s)
    (hΨs : ∀ q : SL(2, ℤ) ⧸ Γ,
      IntegrableOn (fun y : ℝ => Ψ (Quotient.out q)⁻¹ (-(1 / 2) + y * Complex.I)) s)
    (hΦarc : ∀ q : SL(2, ℤ) ⧸ Γ, IntervalIntegrable (fun θ : ℝ =>
      Φ (Quotient.out q)⁻¹ (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I)))
      volume (Real.pi / 3) (2 * Real.pi / 3))
    (hΨarc : ∀ q : SL(2, ℤ) ⧸ Γ, IntervalIntegrable (fun θ : ℝ =>
      Ψ (Quotient.out q)⁻¹ (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I)))
      volume (Real.pi / 3) (2 * Real.pi / 3)) :
    (∑ q : SL(2, ℤ) ⧸ Γ, ∫ y in s, Φ (Quotient.out q)⁻¹ (1 / 2 + y * Complex.I)) =
        (∑ q : SL(2, ℤ) ⧸ Γ, ∫ y in s, Φ (Quotient.out q)⁻¹ (-(1 / 2) + y * Complex.I)) +
          ∑ q : SL(2, ℤ) ⧸ Γ,
            c ((Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q) *
              ∫ y in s, Ψ (Quotient.out q)⁻¹ (-(1 / 2) + y * Complex.I) ∧
      2 * (∑ q : SL(2, ℤ) ⧸ Γ, ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
          Φ (Quotient.out q)⁻¹ (Complex.exp (θ * Complex.I)) *
            (Complex.I * Complex.exp (θ * Complex.I))) =
        -∑ q : SL(2, ℤ) ⧸ Γ,
          c ((Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q) *
            ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
              Ψ (Quotient.out q)⁻¹ (Complex.exp (θ * Complex.I)) *
                (Complex.I * Complex.exp (θ * Complex.I)) := by sorry
