-- Prove2me | Theorems.Thm_HolevoEntropyGain_eq_30
-- name    : HolevoEntropyGain.eq_30
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:21:16.431623+00:00
-- url     : https://prove2.me/theorems/9d6567f3-f080-4555-92f4-fe6139a92122
-- title:
--   Eqs. (28)–(30): $H(\Phi[\rho_\beta]) - H(\rho_\beta)\to\log|\det K|$ as $\beta\to0$
-- statement:
--   Under the hypotheses of Proposition 2, let $F = R\epsilon R^\top$ with $\epsilon$ real positive definite and let $\rho_\beta = \exp(-\beta F - c(\beta))$ be its Gibbs states. Then for every $\beta>0$ both $H(\rho_\beta)$ and $H(\Phi[\rho_\beta])$ are finite, and the bound (27) is achieved asymptotically:
--
--   $$
--   H(\Phi[\rho_\beta]) - H(\rho_\beta) \longrightarrow \log|\det K| \qquad (\beta\to0^+). \tag{30}
--   $$
--
--   This is the upper half of (21).
--
--   Differences from the source:
--   - encoding: a separable Hilbert space H carrying a representation of the CCR → ℓ²(I) with [Countable I] [Nonempty I]; reason: a representation space is nonzero and separable; on ℓ²(∅) = 0 there are no states and the statement would be about an empty set
--   - reading: the Weyl system giving the representation of the CCR → an irreducible, strongly continuous Weyl system (WeylSystem); reason: the Schrödinger representation (Stone–von Neumann); under the reducible reading Proposition 2 is false (W ⊗ I with id ⊗ trace-and-prepare)
--   - encoding: W(z) = exp(iRz) on Z of dimension 2s with commutation matrix Δ → W(z)W(w) = exp(−(i/2)zᵀΔw)W(z+w), Z = Fin (2*s) → ℝ, every nondegenerate skew-symmetric Δ; reason: [Rⱼ, Rₖ] = iΔⱼₖ; every statement is invariant under Δ ↦ −Δ, so the sign convention changes no instance
--   - encoding: Φ*(W(z)) = W(Kz)exp(−½zᵀμz) with μ ≥ ±(i/2)(Δ − KᵀΔK) (15) → Tr Φ[X]W(z) = Tr X W(Kz)·exp(−½zᵀμz) for every trace-class X, and (15) as two complex PosSemidef conditions; reason: Φ* is normal and the Weyl operators generate the bounded operators weakly, so the predual law is equivalent
--   - encoding: F = RεRᵀ → spectral data (orthonormal basis eₙ, energies Eₙ) whose form equals Σⱼₖ εⱼₖ⟨Rⱼψ, Rₖψ⟩ on ∩ⱼ D(Rⱼ), Rⱼ the Stone generator of t ↦ W(teⱼ); the statement holds for every such datum; reason: Mathlib has no unbounded functional calculus; (5) forces discrete spectrum, so F has such data and every choice gives the same exp(−βF)
--   - reading: "∼" as β → 0 → a limit along β ↓ 0 (𝓝[>] 0); reason: the target is finite, so asymptotic equivalence is a limit; β > 0 throughout, as in (6)
--   - encoding: H(ρ) = Σλₖ(−log λₖ) and H(ρ‖σ) = Σλₖ[log λₖ − ⟨eₖ|log σ|eₖ⟩] in [0, +∞] → extendedEntropyNats / extendedRelativeEntropyNats, suprema over finite coordinate compressions in ℝ≥0∞; reason: equal for density operators by Lindblad's lemma; natural logarithm as in footnote 1
--   - encoding: the difference of two finite entropies → difference of the toReal values, after the finiteness clauses; reason: the finiteness clauses make toReal the entropies
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, proof of Proposition 2, eqs. (28)–(30), pp.6–7

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_HolevoEntropyGain_IsCommutationMatrix
import Definitions.Def_HolevoEntropyGain_IsGaussianChannel
import Definitions.Def_HolevoEntropyGain_IsEnergySpectrum
import Definitions.Def_HolevoEntropyGain_gibbsState

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)
open Filter Topology

namespace HolevoEntropyGain

/-- Equations (28)–(30): the bound (27) is achieved asymptotically for the states `ρ_β`, `β → 0`:
`H(ρ_β)` and `H(Φ[ρ_β])` are finite for `β > 0`, and `H(Φ[ρ_β]) - H(ρ_β) → log |det K|`
(Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, proof of Proposition 2, eqs. (28)–(30), pp.6–7, PDF pp.6–7).

**Formalization Note** "∼" in (30) has a finite target and is read as a limit (R7). The finiteness
clauses make the `toReal` values the real entropies. The theorem is for every spectral datum of
`F = RεRᵀ` (R10). -/
theorem eq_30 {I : Type} [Countable I] [Nonempty I] {s : ℕ}
    {Δ : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ} (hΔ : IsCommutationMatrix Δ) (W : WeylSystem I Δ)
    {K μ : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ} {Φ : Channel I I}
    (hΦ : IsGaussianChannel W K μ Φ) (hK : K.det ≠ 0)
    {ε : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ} (hε : ε.PosDef)
    {e : HilbertBasis I ℂ (Hilbert I)} {E : I → ℝ} (hE : IsEnergySpectrum W ε e E) :
    (∀ β : ℝ, 0 < β → extendedEntropyNats (gibbsState e E β) < ⊤ ∧
      extendedEntropyNats (Φ.val (gibbsState e E β)) < ⊤) ∧
    Tendsto (fun β => (extendedEntropyNats (Φ.val (gibbsState e E β))).toReal -
        (extendedEntropyNats (gibbsState e E β)).toReal) (𝓝[>] 0) (𝓝 (Real.log |K.det|)) := by sorry

end HolevoEntropyGain
