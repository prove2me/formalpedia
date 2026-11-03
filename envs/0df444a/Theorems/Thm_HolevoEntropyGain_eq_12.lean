-- Prove2me | Theorems.Thm_HolevoEntropyGain_eq_12
-- name    : HolevoEntropyGain.eq_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:19:12.515134+00:00
-- url     : https://prove2.me/theorems/19cc0bc0-bc20-4dce-9943-ceb15fe822b6
-- title:
--   Eq. (12): $-\log\|\Phi[I]\| \le G(\Phi)$
-- statement:
--   Let $\Phi$ be a regular channel on a separable Hilbert space with $\Phi[I] = A$. Then
--
--   $$
--   -\log\|\Phi[I]\| \le G(\Phi), \tag{12}
--   $$
--
--   where $G(\Phi) = \inf_{\rho:H(\rho)<\infty}(H(\Phi[\rho])-H(\rho))$ is the minimal entropy gain. In particular a unital channel ($\Phi[I] = I$) has $G(\Phi)\ge0$.
--
--   **Formalization Note** $\|\Phi[I]\|>0$ is a consequence of trace preservation on a nonzero space, not a hypothesis; on the zero space $\ell^2(\emptyset)$ the statement reads $0\le+\infty$.
--
--   Differences from the source:
--   - encoding: a separable Hilbert space H; operators on it → ℓ²(I) for a type I with [Countable I], operators as coefficient arrays in the canonical basis; reason: every separable Hilbert space is unitarily ℓ²(I) for a countable I; the same instances
--   - encoding: H(ρ) = Σλₖ(−log λₖ) and H(ρ‖σ) = Σλₖ[log λₖ − ⟨eₖ|log σ|eₖ⟩] in [0, +∞] → extendedEntropyNats / extendedRelativeEntropyNats, suprema over finite coordinate compressions in ℝ≥0∞; reason: equal for density operators by Lindblad's lemma; natural logarithm as in footnote 1
--   - encoding: entropy gain H(Φ[ρ]) − H(ρ) in (−∞, +∞] for H(ρ) < ∞ → difference of the two entropies coerced to EReal; reason: H(ρ) is finite, so no ∞ − ∞ occurs; the same value
--   - encoding: Φ regular with Φ[I] = A: some Kraus representation with Σⱼ VⱼVⱼ* ↑ A → IsRegularWith Φ A: A positive and some countable Kraus family with Σⱼ‖Vⱼ*ψ‖² = ⟨ψ, Aψ⟩ for all ψ; reason: increasing positive partial sums converge weakly to A exactly when their quadratic forms do
--   - encoding: G(Φ) = inf over states with H(ρ) < ∞ (11), in (−∞, +∞] → minimalEntropyGain, an infimum in EReal over the subtype {ρ // H ρ < ⊤}; reason: the same infimum; EReal holds the value +∞
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §2, eq. (12), p.4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters
import Definitions.Def_HolevoEntropyGain_minimalEntropyGain
import Definitions.Def_HolevoEntropyGain_IsRegularWith

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)

namespace HolevoEntropyGain

/-- Equation (12): `-log ‖Φ[I]‖ ≤ G(Φ)` for a regular channel `Φ`
(Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §2, eq. (12), p.4, PDF p.4).

**Formalization Note** `‖Φ[I]‖ > 0` follows from `∑ⱼ Vⱼ*Vⱼ = I` on a nonzero space and is not a
hypothesis. On `Hilbert I = 0` the statement reads `-log 0 = 0 ≤ ⊤`. -/
theorem eq_12 {I : Type} [Countable I] {Φ : Channel I I} {A : Hilbert I →L[ℂ] Hilbert I}
    (hA : IsRegularWith Φ A) :
    ((-Real.log ‖A‖ : ℝ) : EReal) ≤ minimalEntropyGain Φ := by sorry

end HolevoEntropyGain
