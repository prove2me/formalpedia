-- Prove2me | Theorems.Thm_HolevoEntropyGain_proposition_2
-- name    : HolevoEntropyGain.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:21:33.666799+00:00
-- url     : https://prove2.me/theorems/8e059b2f-fc4a-41f8-ad26-221130f06e31
-- title:
--   Proposition 2: a Gaussian channel with $\det K\ne0$ is regular, $\Phi[I] = |\det K|^{-1}I$, and $G(\Phi) = \log|\det K|$
-- statement:
--   Let $(Z,\Delta)$ be a coordinate symplectic space, $\dim Z = 2s$, with nondegenerate skew-symmetric commutation matrix $\Delta$, and let $W(z) = \exp(iRz)$ be the (irreducible, strongly continuous) Weyl system on a separable Hilbert space $H$. Let $\Phi$ be a centered Bosonic Gaussian channel,
--
--   $$
--   \Phi^*(W(z)) = W(Kz)\exp\!\Big(-\tfrac12 z^\top\mu z\Big),
--   $$
--
--   where the real positive semidefinite matrix $\mu$ satisfies $\mu\ge\pm\frac i2(\Delta-K^\top\Delta K)$ (15). If the matrix $K$ is nondegenerate, then
--
--   1. $\Phi$ is regular with
--   $$
--   \Phi[I] = |\det K|^{-1} I; \tag{20}
--   $$
--   that is, for some — and in fact for every — countable Kraus representation $\Phi[\rho] = \sum_jV_j\rho V_j^*$ one has $\sum_j\|V_j^*\psi\|^2 = |\det K|^{-1}\|\psi\|^2$ for all $\psi\in H$;
--   2. the minimal entropy gain is
--   $$
--   G(\Phi) = \log|\det K|. \tag{21}
--   $$
--
--   Since $\log|\det K|$ takes every real value (for one mode, the attenuator, the amplifier and the additive-noise channel give $\log k^2$), infinite-dimensional channels can have positive minimal entropy gain, unlike finite-dimensional ones, for which $G(\Phi)\le0$. The entropy gain is governed by the factor by which the channel changes phase-space volume.
--
--   Differences from the source:
--   - encoding: a separable Hilbert space H carrying a representation of the CCR → ℓ²(I) with [Countable I] [Nonempty I]; reason: a representation space is nonzero and separable; on ℓ²(∅) = 0 there are no states and the statement would be about an empty set
--   - reading: the Weyl system giving the representation of the CCR → an irreducible, strongly continuous Weyl system (WeylSystem); reason: the Schrödinger representation (Stone–von Neumann); under the reducible reading Proposition 2 is false (W ⊗ I with id ⊗ trace-and-prepare)
--   - encoding: W(z) = exp(iRz) on Z of dimension 2s with commutation matrix Δ → W(z)W(w) = exp(−(i/2)zᵀΔw)W(z+w), Z = Fin (2*s) → ℝ, every nondegenerate skew-symmetric Δ; reason: [Rⱼ, Rₖ] = iΔⱼₖ; every statement is invariant under Δ ↦ −Δ, so the sign convention changes no instance
--   - encoding: Φ*(W(z)) = W(Kz)exp(−½zᵀμz) with μ ≥ ±(i/2)(Δ − KᵀΔK) (15) → Tr Φ[X]W(z) = Tr X W(Kz)·exp(−½zᵀμz) for every trace-class X, and (15) as two complex PosSemidef conditions; reason: Φ* is normal and the Weyl operators generate the bounded operators weakly, so the predual law is equivalent
--   - encoding: H(ρ) = Σλₖ(−log λₖ) and H(ρ‖σ) = Σλₖ[log λₖ − ⟨eₖ|log σ|eₖ⟩] in [0, +∞] → extendedEntropyNats / extendedRelativeEntropyNats, suprema over finite coordinate compressions in ℝ≥0∞; reason: equal for density operators by Lindblad's lemma; natural logarithm as in footnote 1
--   - encoding: Φ regular with Φ[I] = |det K|⁻¹I → IsRegularWith Φ (|det K|⁻¹ • id): some countable Kraus family with Σⱼ‖Vⱼ*ψ‖² = |det K|⁻¹‖ψ‖²; reason: increasing positive partial sums converge weakly to A exactly when their quadratic forms do
--   - generalization: (20) for the Kraus representation defining Φ[I] (p.2: it does not depend on the choice) → (20) also for every countable Kraus representation of Φ; reason: contains the printed (∃) statement as its first clause; the paper's own remark on p.2 asserts the independence
--   - encoding: G(Φ) of (11), in (−∞, +∞] → minimalEntropyGain, an infimum in EReal, equal to the coercion of Real.log |det K|; reason: the same infimum; det K ≠ 0 so the logarithm is of a positive number
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, Proposition 2, eqs. (20)–(21), p.5

import Mathlib
import Definitions.Def_HolevoEntropyGain_IsCommutationMatrix
import Definitions.Def_HolevoEntropyGain_IsGaussianChannel
import Definitions.Def_HolevoEntropyGain_IsRegularWith
import Definitions.Def_HolevoEntropyGain_minimalEntropyGain

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Frontier18.P18 (IsKrausRepresentation)

namespace HolevoEntropyGain

/-- Proposition 2: let `Φ` be a centered Bosonic Gaussian channel with nondegenerate `K`. Then `Φ` is
regular with `Φ[I] = |det K|⁻¹I` (20), and `G(Φ) = log |det K|` (21)
(Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, Proposition 2, eqs. (20)–(21), p.5, PDF p.5).

**Formalization Note** (20) is stated for some Kraus representation and for every countable one (R5);
p.2 notes that `Φ[I]` does not depend on the choice. There is no regularity hypothesis.
`[Nonempty I]`, `[Countable I]`: the representation space is nonzero and separable. The statement holds
for every nondegenerate skew-symmetric `Δ`, not only (22), and for every `μ` with (15). -/
theorem proposition_2 {I : Type} [Countable I] [Nonempty I] {s : ℕ}
    {Δ : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ} (hΔ : IsCommutationMatrix Δ) (W : WeylSystem I Δ)
    {K μ : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ} {Φ : Channel I I}
    (hΦ : IsGaussianChannel W K μ Φ) (hK : K.det ≠ 0) :
    IsRegularWith Φ (((|K.det|)⁻¹ : ℝ) • ContinuousLinearMap.id ℂ (Hilbert I)) ∧
      (∀ (J : Type) [Countable J] (V : J → (Hilbert I →L[ℂ] Hilbert I)),
        IsKrausRepresentation Φ.val V → ∀ ψ : Hilbert I,
          HasSum (fun j => ‖ContinuousLinearMap.adjoint (V j) ψ‖ ^ 2) ((|K.det|)⁻¹ * ‖ψ‖ ^ 2)) ∧
      minimalEntropyGain Φ = ((Real.log |K.det| : ℝ) : EReal) := by sorry

end HolevoEntropyGain
