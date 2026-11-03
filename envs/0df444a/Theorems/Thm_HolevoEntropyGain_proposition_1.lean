-- Prove2me | Theorems.Thm_HolevoEntropyGain_proposition_1
-- name    : HolevoEntropyGain.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:18:46.759283+00:00
-- url     : https://prove2.me/theorems/6ff90ee6-545f-4a25-ae71-bbe95a35dfc3
-- title:
--   Proposition 1: $H(\Phi[\rho]) - H(\rho) \ge \operatorname{Tr}\Phi[\rho](-\log\Phi[I])$
-- statement:
--   Let $\Phi$ be a regular channel on a separable Hilbert space, with $\Phi[I]$ the positive bounded operator $\sum_jV_jV_j^*$, and let $\rho$ be a state with finite entropy. Then
--
--   $$
--   H(\Phi[\rho]) - H(\rho) \ge \operatorname{Tr}\Phi[\rho](-\log\Phi[I]), \tag{7}
--   $$
--
--   where on the right stands the extended quantum expectation of the operator $-\log\Phi[I]$, which is selfadjoint and bounded from below (and may be $+\infty$).
--
--   This is the paper's new lower bound for the entropy gain. It is the infinite-dimensional replacement of the finite-dimensional bound $-\log d$, and it gives (12).
--
--   Differences from the source:
--   - encoding: a separable Hilbert space H; operators on it → ℓ²(I) for a type I with [Countable I], operators as coefficient arrays in the canonical basis; reason: every separable Hilbert space is unitarily ℓ²(I) for a countable I; the same instances
--   - encoding: H(ρ) = Σλₖ(−log λₖ) and H(ρ‖σ) = Σλₖ[log λₖ − ⟨eₖ|log σ|eₖ⟩] in [0, +∞] → extendedEntropyNats / extendedRelativeEntropyNats, suprema over finite coordinate compressions in ℝ≥0∞; reason: equal for density operators by Lindblad's lemma; natural logarithm as in footnote 1
--   - encoding: entropy gain H(Φ[ρ]) − H(ρ) in (−∞, +∞] for H(ρ) < ∞ → difference of the two entropies coerced to EReal; reason: H(ρ) is finite, so no ∞ − ∞ occurs; the same value
--   - encoding: the extended expectation (3) of −log A for positive bounded A → sup over ε > 0 of Tr ρ(−log(A + εI)) in EReal, by continuous functional calculus; reason: equals (3) by monotone convergence in the spectral measure of A; +∞ on ker A as in the paper
--   - encoding: Φ regular with Φ[I] = A: some Kraus representation with Σⱼ VⱼVⱼ* ↑ A → IsRegularWith Φ A: A positive and some countable Kraus family with Σⱼ‖Vⱼ*ψ‖² = ⟨ψ, Aψ⟩ for all ψ; reason: increasing positive partial sums converge weakly to A exactly when their quadratic forms do
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §2, Proposition 1, eq. (7), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters
import Definitions.Def_HolevoEntropyGain_entropyGain
import Definitions.Def_HolevoEntropyGain_IsRegularWith
import Definitions.Def_HolevoEntropyGain_extendedExpectation

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)

namespace HolevoEntropyGain

/-- Proposition 1: for a regular channel `Φ` and a state `ρ` with finite entropy,
`H(Φ[ρ]) - H(ρ) ≥ Tr Φ[ρ](-log Φ[I])`, with the extended expectation on the right
(Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §2, Proposition 1, eq. (7), p.3, PDF p.3).

**Formalization Note** `A` is `Φ[I]` (`IsRegularWith`). The hypothesis uses one Kraus representation,
which is the weakest form (R5). -/
theorem proposition_1 {I : Type} [Countable I] {Φ : Channel I I}
    {A : Hilbert I →L[ℂ] Hilbert I} (hA : IsRegularWith Φ A) (ρ : State I)
    (hρ : extendedEntropyNats ρ.coefficients < ⊤) :
    extendedExpectation (Φ.val ρ.coefficients) A ≤ entropyGain Φ ρ := by sorry

end HolevoEntropyGain
