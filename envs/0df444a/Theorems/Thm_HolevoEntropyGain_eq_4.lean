-- Prove2me | Theorems.Thm_HolevoEntropyGain_eq_4
-- name    : HolevoEntropyGain.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:18:24.909514+00:00
-- url     : https://prove2.me/theorems/38628500-4c34-4759-9d1e-871c0177b3ac
-- title:
--   Eq. (4): $H(\rho\|\sigma) + H(\rho) = \operatorname{Tr}\rho(-\log\sigma)$
-- statement:
--   Let $\rho,\sigma$ be density operators on a separable Hilbert space. Then
--
--   $$
--   H(\rho\|\sigma) + H(\rho) = \operatorname{Tr}\rho(-\log\sigma), \tag{4}
--   $$
--
--   where $H(\rho\|\sigma)$ is the relative entropy, $H(\rho)$ the von Neumann entropy, and the right side is the extended expectation of the operator $-\log\sigma\ge0$ (equal to $+\infty$ on the kernel of $\sigma$). Both sides are nonnegative but can be infinite.
--
--   The identity converts monotonicity of the relative entropy into an inequality between entropies and expectations; it is the first step of the proof of Proposition 1.
--
--   Differences from the source:
--   - encoding: a separable Hilbert space H; operators on it → ℓ²(I) for a type I with [Countable I], operators as coefficient arrays in the canonical basis; reason: every separable Hilbert space is unitarily ℓ²(I) for a countable I; the same instances
--   - encoding: H(ρ) = Σλₖ(−log λₖ) and H(ρ‖σ) = Σλₖ[log λₖ − ⟨eₖ|log σ|eₖ⟩] in [0, +∞] → extendedEntropyNats / extendedRelativeEntropyNats, suprema over finite coordinate compressions in ℝ≥0∞; reason: equal for density operators by Lindblad's lemma; natural logarithm as in footnote 1
--   - encoding: the extended expectation (3) of −log A for positive bounded A → sup over ε > 0 of Tr ρ(−log(A + εI)) in EReal, by continuous functional calculus; reason: equals (3) by monotone convergence in the spectral measure of A; +∞ on ker A as in the paper
--   - encoding: both sides in [0, +∞] → the left side is a sum in ℝ≥0∞ coerced to EReal; reason: the extended expectation lives in EReal; the coercion is injective and order preserving
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §2, eq. (4), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P18
import Definitions.Def_HolevoEntropyGain_extendedExpectation

open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats extendedRelativeEntropyNats)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator)

namespace HolevoEntropyGain

/-- Equation (4): for density operators `ρ, σ`, `H(ρ‖σ) + H(ρ) = Tr ρ(-log σ)`, where both sides are
nonnegative but can be infinite (Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §2, eq. (4), p.3, PDF p.3).

**Formalization Note** The left side is a sum in `[0, ∞]`, cast to `EReal`, so that both sides live in
the same type. The right side is the extended expectation of `-log σ`, which is `+∞` on `ker σ`. -/
theorem eq_4 {I : Type} [Countable I] (ρ σ : State I) :
    (extendedRelativeEntropyNats ρ.coefficients σ.coefficients +
        extendedEntropyNats ρ.coefficients).toEReal =
      extendedExpectation ρ.coefficients (boundedOperator σ.coefficients) := by sorry

end HolevoEntropyGain
