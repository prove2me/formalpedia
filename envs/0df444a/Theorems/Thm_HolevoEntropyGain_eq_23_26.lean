-- Prove2me | Theorems.Thm_HolevoEntropyGain_eq_23_26
-- name    : HolevoEntropyGain.eq_23_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:21:11.671205+00:00
-- url     : https://prove2.me/theorems/cd4a18bc-e844-43f4-a6ef-c10337725c88
-- title:
--   Eqs. (23)–(26): $\Phi[\exp(-\beta F)]\to|\det K|^{-1}I$ weakly as $\beta\to0$
-- statement:
--   Let $W$ be an irreducible strongly continuous Weyl system for a nondegenerate skew-symmetric $\Delta$, $\Phi$ a centered Bosonic Gaussian channel with parameters $K,\mu$ satisfying (15), and $\det K\neq0$. Let $F = R\epsilon R^\top$ with $\epsilon$ real positive definite. Then, as $\beta\to0^+$, the operators $\Phi[\exp(-\beta F)]$ converge to $|\det K|^{-1}W(0) = |\det K|^{-1}I$ in the weak operator topology:
--
--   $$
--   \langle\psi,\Phi[\exp(-\beta F)]\varphi\rangle \longrightarrow |\det K|^{-1}\langle\psi,\varphi\rangle \qquad\text{for all }\psi,\varphi .
--   $$
--
--   This summarizes (23), (24) and (26) of the proof of Proposition 2, and gives (20).
--
--   **Formalization Note** $\exp(-\beta F)$ is trace class by (5) (Lemma 2), so $\Phi[\exp(-\beta F)]$ is trace class and its bounded realization is used.
--
--   Differences from the source:
--   - encoding: a separable Hilbert space H carrying a representation of the CCR → ℓ²(I) with [Countable I] [Nonempty I]; reason: a representation space is nonzero and separable; on ℓ²(∅) = 0 there are no states and the statement would be about an empty set
--   - reading: the Weyl system giving the representation of the CCR → an irreducible, strongly continuous Weyl system (WeylSystem); reason: the Schrödinger representation (Stone–von Neumann); under the reducible reading Proposition 2 is false (W ⊗ I with id ⊗ trace-and-prepare)
--   - encoding: W(z) = exp(iRz) on Z of dimension 2s with commutation matrix Δ → W(z)W(w) = exp(−(i/2)zᵀΔw)W(z+w), Z = Fin (2*s) → ℝ, every nondegenerate skew-symmetric Δ; reason: [Rⱼ, Rₖ] = iΔⱼₖ; every statement is invariant under Δ ↦ −Δ, so the sign convention changes no instance
--   - encoding: Φ*(W(z)) = W(Kz)exp(−½zᵀμz) with μ ≥ ±(i/2)(Δ − KᵀΔK) (15) → Tr Φ[X]W(z) = Tr X W(Kz)·exp(−½zᵀμz) for every trace-class X, and (15) as two complex PosSemidef conditions; reason: Φ* is normal and the Weyl operators generate the bounded operators weakly, so the predual law is equivalent
--   - encoding: F = RεRᵀ → spectral data (orthonormal basis eₙ, energies Eₙ) whose form equals Σⱼₖ εⱼₖ⟨Rⱼψ, Rₖψ⟩ on ∩ⱼ D(Rⱼ), Rⱼ the Stone generator of t ↦ W(teⱼ); the statement holds for every such datum; reason: Mathlib has no unbounded functional calculus; (5) forces discrete spectrum, so F has such data and every choice gives the same exp(−βF)
--   - reading: converge in the weak operator topology as β → 0 → for all ψ, φ, ⟨ψ, Φ[exp(−βF)]φ⟩ → |det K|⁻¹⟨ψ, φ⟩ along β ↓ 0; reason: the definition of weak operator convergence; β > 0 as in (6)
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, proof of Proposition 2, eqs. (23)–(26), p.6

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P18
import Definitions.Def_HolevoEntropyGain_IsCommutationMatrix
import Definitions.Def_HolevoEntropyGain_IsGaussianChannel
import Definitions.Def_HolevoEntropyGain_IsEnergySpectrum
import Definitions.Def_HolevoEntropyGain_gibbsOperator

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator)
open Filter Topology

namespace HolevoEntropyGain

/-- Equations (23)–(26): the operators `Φ[exp(-βF)]`, for `F = RεRᵀ`, converge to `|det K|⁻¹W(0)` in the
weak operator topology as `β → 0` (Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, proof of Proposition 2, eqs. (23)–(26), p.6, PDF p.6).

**Formalization Note** `W(0) = I` (p.6). `exp(-βF)` is trace class by (5) (Lemma 2), so `Φ[exp(-βF)]` is
trace class and `boundedOperator` is its realization. The limit is one-sided, `β ↓ 0`, for all `ψ, φ`
(R7). The theorem is for every spectral datum of `F` (R10). -/
theorem eq_23_26 {I : Type} [Countable I] [Nonempty I] {s : ℕ}
    {Δ : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ} (hΔ : IsCommutationMatrix Δ) (W : WeylSystem I Δ)
    {K μ : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ} {Φ : Channel I I}
    (hΦ : IsGaussianChannel W K μ Φ) (hK : K.det ≠ 0)
    {ε : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ} (hε : ε.PosDef)
    {e : HilbertBasis I ℂ (Hilbert I)} {E : I → ℝ} (hE : IsEnergySpectrum W ε e E)
    (ψ φ : Hilbert I) :
    Tendsto (fun β => inner ℂ ψ (boundedOperator (Φ.val (gibbsOperator e E β)) φ)) (𝓝[>] 0)
      (𝓝 ((((|K.det|)⁻¹ : ℝ) : ℂ) * inner ℂ ψ φ)) := by sorry

end HolevoEntropyGain
