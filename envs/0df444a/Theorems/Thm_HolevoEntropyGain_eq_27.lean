-- Prove2me | Theorems.Thm_HolevoEntropyGain_eq_27
-- name    : HolevoEntropyGain.eq_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:20:57.962821+00:00
-- url     : https://prove2.me/theorems/4fc92fbe-8630-4c16-8c20-d2ecb6a3621d
-- title:
--   Eq. (27): $H(\Phi[\rho]) - H(\rho) \ge \log|\det K|$
-- statement:
--   Let $W$ be an irreducible strongly continuous Weyl system for a nondegenerate skew-symmetric $\Delta$, and $\Phi$ a centered Bosonic Gaussian channel with parameters $K,\mu$ satisfying (15), with $\det K\ne0$. Then
--
--   $$
--   H(\Phi[\rho]) - H(\rho) \ge \log|\det K| \tag{27}
--   $$
--
--   for any state $\rho$ with finite entropy. This is the lower half of (21), obtained from (20) and Proposition 1.
--
--   Differences from the source:
--   - encoding: a separable Hilbert space H carrying a representation of the CCR → ℓ²(I) with [Countable I] [Nonempty I]; reason: a representation space is nonzero and separable; on ℓ²(∅) = 0 there are no states and the statement would be about an empty set
--   - reading: the Weyl system giving the representation of the CCR → an irreducible, strongly continuous Weyl system (WeylSystem); reason: the Schrödinger representation (Stone–von Neumann); under the reducible reading Proposition 2 is false (W ⊗ I with id ⊗ trace-and-prepare)
--   - encoding: W(z) = exp(iRz) on Z of dimension 2s with commutation matrix Δ → W(z)W(w) = exp(−(i/2)zᵀΔw)W(z+w), Z = Fin (2*s) → ℝ, every nondegenerate skew-symmetric Δ; reason: [Rⱼ, Rₖ] = iΔⱼₖ; every statement is invariant under Δ ↦ −Δ, so the sign convention changes no instance
--   - encoding: Φ*(W(z)) = W(Kz)exp(−½zᵀμz) with μ ≥ ±(i/2)(Δ − KᵀΔK) (15) → Tr Φ[X]W(z) = Tr X W(Kz)·exp(−½zᵀμz) for every trace-class X, and (15) as two complex PosSemidef conditions; reason: Φ* is normal and the Weyl operators generate the bounded operators weakly, so the predual law is equivalent
--   - encoding: H(ρ) = Σλₖ(−log λₖ) and H(ρ‖σ) = Σλₖ[log λₖ − ⟨eₖ|log σ|eₖ⟩] in [0, +∞] → extendedEntropyNats / extendedRelativeEntropyNats, suprema over finite coordinate compressions in ℝ≥0∞; reason: equal for density operators by Lindblad's lemma; natural logarithm as in footnote 1
--   - encoding: entropy gain H(Φ[ρ]) − H(ρ) in (−∞, +∞] for H(ρ) < ∞ → difference of the two entropies coerced to EReal; reason: H(ρ) is finite, so no ∞ − ∞ occurs; the same value
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, proof of Proposition 2, eq. (27), p.6

import Mathlib
import Definitions.Def_HolevoEntropyGain_IsCommutationMatrix
import Definitions.Def_HolevoEntropyGain_IsGaussianChannel
import Definitions.Def_HolevoEntropyGain_entropyGain

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)

namespace HolevoEntropyGain

/-- Equation (27): `H(Φ[ρ]) - H(ρ) ≥ log |det K|` for any state `ρ` with finite entropy, for a Bosonic
Gaussian channel with nondegenerate `K` (Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, proof of Proposition 2, eq. (27), p.6, PDF p.6). -/
theorem eq_27 {I : Type} [Countable I] [Nonempty I] {s : ℕ}
    {Δ : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ} (hΔ : IsCommutationMatrix Δ) (W : WeylSystem I Δ)
    {K μ : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ} {Φ : Channel I I}
    (hΦ : IsGaussianChannel W K μ Φ) (hK : K.det ≠ 0)
    (ρ : State I) (hρ : extendedEntropyNats ρ.coefficients < ⊤) :
    ((Real.log |K.det| : ℝ) : EReal) ≤ entropyGain Φ ρ := by sorry

end HolevoEntropyGain
