-- Prove2me | Theorems.Thm_HolevoEntropyGain_finite_entropy_energy_operator
-- name    : HolevoEntropyGain.finite_entropy_energy_operator
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:17:31.408851+00:00
-- url     : https://prove2.me/theorems/110ec627-390a-4ed3-8f23-791130bf66f3
-- title:
--   Every finite-entropy state has an energy operator $F$ with $\operatorname{Tr}\rho F<\infty$ and $\operatorname{Tr}e^{-\beta F}<\infty$
-- statement:
--   Let $\rho$ be a density operator on a separable Hilbert space with finite entropy $H(\rho) = \sum_k\lambda_k(-\log\lambda_k)<\infty$. Then there is a positive selfadjoint operator $F$, with an orthonormal eigenbasis $(e_n)$ and eigenvalues $E_n\ge0$, such that
--
--   $$
--   \operatorname{Tr}\exp(-\beta F) = \sum_n e^{-\beta E_n} < \infty \quad (\beta>0), \tag{5}
--   $$
--
--   and
--
--   $$
--   \operatorname{Tr}\rho F = \sum_n E_n\,\langle e_n|\rho|e_n\rangle < +\infty .
--   $$
--
--   This is the device that lets the proof of Proposition 1 compare $\rho$ with the Gibbs states $\rho_\beta$ of $F$: the relative entropy $H(\rho\|\rho_\beta)$ is then finite.
--
--   Differences from the source:
--   - encoding: a separable Hilbert space H; operators on it → ℓ²(I) for a type I with [Countable I], operators as coefficient arrays in the canonical basis; reason: every separable Hilbert space is unitarily ℓ²(I) for a countable I; the same instances
--   - encoding: H(ρ) = Σλₖ(−log λₖ) and H(ρ‖σ) = Σλₖ[log λₖ − ⟨eₖ|log σ|eₖ⟩] in [0, +∞] → extendedEntropyNats / extendedRelativeEntropyNats, suprema over finite coordinate compressions in ℝ≥0∞; reason: equal for density operators by Lindblad's lemma; natural logarithm as in footnote 1
--   - encoding: an operator F ≥ 0 with Tr ρF < +∞ and (5) → an orthonormal basis (eₙ) indexed by I and Eₙ ≥ 0 with Σₙ e^{−βEₙ} summable for β > 0 and Σₙ Eₙ⟨eₙ|ρ|eₙ⟩ < ⊤ in ℝ≥0∞; reason: (5) forces discrete spectrum, so every such F is diagonal in an orthonormal basis; Tr ρF of (3) equals Σₙ Eₙ⟨eₙ|ρ|eₙ⟩ by Tonelli
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §2, unnumbered remark after (6), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P18
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Defs_RealLabelRegisters

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)
open QAlgorithms.Papers.Independent.Frontier18.P18 (boundedOperator)

namespace HolevoEntropyGain

/-- Every density operator `ρ` with finite entropy has a positive selfadjoint operator `F` with
`Tr exp(-βF) < ∞` for every `β > 0` (that is (5)) and `Tr ρF < ∞`
(Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §2, unnumbered remark, p.3, PDF p.3).

**Formalization Note** `F` is given by spectral data: (5) forces discrete spectrum, so `F` has an
orthonormal eigenbasis `(eₙ)` with eigenvalues `Eₙ ≥ 0`. `Tr ρF` is `∑ₙ Eₙ⟨eₙ|ρ|eₙ⟩` in `[0, ∞]`, which
equals (3) by Tonelli. `boundedOperator ρ` is the bounded realization of the trace-class array of `ρ`. -/
theorem finite_entropy_energy_operator {I : Type} [Countable I] (ρ : State I)
    (hρ : extendedEntropyNats ρ.coefficients < ⊤) :
    ∃ (e : HilbertBasis I ℂ (Hilbert I)) (E : I → ℝ), (∀ n, 0 ≤ E n) ∧
      (∀ β : ℝ, 0 < β → Summable fun n => Real.exp (-β * E n)) ∧
      (∑' n, ENNReal.ofReal (E n) * ENNReal.ofReal
        (RCLike.re (inner ℂ (e n) (boundedOperator ρ.coefficients (e n))))) < ⊤ := by sorry

end HolevoEntropyGain
