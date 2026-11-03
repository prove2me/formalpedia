-- Prove2me | Theorems.Thm_HolevoEntropyGain_eq_16
-- name    : HolevoEntropyGain.eq_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:21:12.828+00:00
-- url     : https://prove2.me/theorems/5419fd16-a61e-4ffe-8011-4a77bbea276b
-- title:
--   Eq. (16): a Gaussian channel maps covariance $\alpha$ to $K^\top\alpha K + \mu$
-- statement:
--   Let $W$ be an irreducible strongly continuous Weyl system for a nondegenerate skew-symmetric $\Delta$, and $\Phi$ a centered Bosonic Gaussian channel, $\Phi^*(W(z)) = W(Kz)\exp(-\frac12z^\top\mu z)$, with $\mu$ real positive semidefinite satisfying (15). The channel $\Phi$ transforms a Gaussian state with covariance matrix $\alpha$ into the Gaussian state with covariance matrix
--
--   $$
--   \alpha' = K^\top\alpha K + \mu. \tag{16}
--   $$
--
--   Differences from the source:
--   - encoding: a separable Hilbert space H; operators on it → ℓ²(I) for a type I with [Countable I], operators as coefficient arrays in the canonical basis; reason: every separable Hilbert space is unitarily ℓ²(I) for a countable I; the same instances
--   - reading: the Weyl system giving the representation of the CCR → an irreducible, strongly continuous Weyl system (WeylSystem); reason: the Schrödinger representation (Stone–von Neumann); under the reducible reading Proposition 2 is false (W ⊗ I with id ⊗ trace-and-prepare)
--   - encoding: W(z) = exp(iRz) on Z of dimension 2s with commutation matrix Δ → W(z)W(w) = exp(−(i/2)zᵀΔw)W(z+w), Z = Fin (2*s) → ℝ, every nondegenerate skew-symmetric Δ; reason: [Rⱼ, Rₖ] = iΔⱼₖ; every statement is invariant under Δ ↦ −Δ, so the sign convention changes no instance
--   - encoding: Φ*(W(z)) = W(Kz)exp(−½zᵀμz) with μ ≥ ±(i/2)(Δ − KᵀΔK) (15) → Tr Φ[X]W(z) = Tr X W(Kz)·exp(−½zᵀμz) for every trace-class X, and (15) as two complex PosSemidef conditions; reason: Φ* is normal and the Weyl operators generate the bounded operators weakly, so the predual law is equivalent
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, eq. (16), p.5

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_HolevoEntropyGain_IsCommutationMatrix
import Definitions.Def_HolevoEntropyGain_IsGaussianState
import Definitions.Def_HolevoEntropyGain_IsGaussianChannel

open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open Matrix

namespace HolevoEntropyGain

/-- Equation (16): the channel `Φ` transforms a Gaussian state with covariance matrix `α` into a Gaussian
state with covariance matrix `α' = KᵀαK + μ` (Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, eq. (16), p.5, PDF p.5). -/
theorem eq_16 {I : Type} [Countable I] {s : ℕ} {Δ : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ}
    (hΔ : IsCommutationMatrix Δ) (W : WeylSystem I Δ)
    {K μ α : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ} {Φ : Channel I I}
    (hΦ : IsGaussianChannel W K μ Φ) {ρ : Matrix I I ℂ} (hρ : IsGaussianState W α ρ) :
    IsGaussianState W (K.transpose * α * K + μ) (Φ.val ρ) := by sorry

end HolevoEntropyGain
