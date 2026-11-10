-- Prove2me | Theorems.Thm_HoneycombCodes_theorem_1_2
-- name    : HoneycombCodes.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:30:41.633056+00:00
-- url     : https://prove2.me/theorems/ea5e13d6-9281-4635-870e-f7679e7aced5
-- title:
--   Theorem 1.2 — the first honeycomb bound
-- statement:
--   For every $0<\delta<1/2$ the following hold.
--
--   1. **Soundness.** $R_2(\delta)\le\kappa_{HC}(\delta)$.
--   2. **Containment and strict improvement.** $\kappa_{HC}(\delta)\le M_2(\delta)$ and $\kappa_{HC}(\delta)<\kappa_H(\delta)=R_{MQC}(\delta)$.
--   3. **Comparison with moving-projection and channel bounds.** The combined exponent $\kappa_{best}:=\min\{\kappa_{CW},\kappa_{HC}\}$ satisfies
--   $$
--   R_2(\delta)\le\kappa_{best}(\delta)\le\kappa_{bin}(\delta)\le R_{2MQC}(\delta)<M_2(\delta)
--   $$
--   and $\kappa_{best}(\delta)<R_{2MQC}(\delta)$.
--
--   Here $R_2$ is the asymptotic rate of binary codes, $\kappa_{HC}$ the first honeycomb exponent (Definition 1.1), $M_2$ the second MRRW exponent, $\kappa_H$ and $\kappa_{CW}$ the whole-cube and constant-weight exponents of OpenAI's moving-projection method, $\kappa_{bin}=\min\{\kappa_H,\kappa_{CW}\}$, and $R_{MQC}$, $R_{2MQC}$ the mixed-qubit-channel exponents of Alrabiah and Guruswami.
--
--   The theorem places the honeycomb bound below both earlier 2026 improvements of $M_2$ and strictly below 2MQC at every distance.
--
--   **Formalization Note** Every exponent is a real infimum over its printed feasible set with the printed strict constraints.
--
--   Differences from the source:
--
--   - encoding: binary codes C ⊆ {±1}ⁿ and R₂(δ) = lim sup (1/n) log₂ A₂(n, ⌈δn⌉) → the published PrettyGoodCriterion.rateFunction (codes as Finsets of words Fin n → Fin 2, Real.logb 2, real Filter.limsup); reason: {±1} and Fin 2 are in bijection and Hamming distance is preserved; the sequence lies in [0, 1], so the real lim sup is the true one
--   - reading: the MQC and 2MQC exponents of [AG26] (recalled in Appendix D) → R_MQC and R_2MQC defined by the paper's normalized displays (119) and (122)–(124), with λ_δ(0,0) = 2δ; reason: Theorem 1.2 refers to App. D for these exponents; the normalized displays are the only definitions this paper states
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), Theorem 1.2, p.4 (PDF 6)

import Mathlib
import Definitions.Def_HoneycombCodes_kappaHC
import Definitions.Def_HoneycombCodes_R2MQC
import Definitions.Def_HoneycombCodes_RMQC
import Definitions.Def_HoneycombCodes_M2
import Definitions.Def_PrettyGoodCriterion_rateFunction

set_option autoImplicit false

namespace HoneycombCodes

/-- **Theorem 1.2 (The first honeycomb bound)**, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), p.4 (PDF 6). For every `0 < δ < 1/2`:
(i) (Soundness) `R₂(δ) ≤ κ_HC(δ)`.
(ii) (Containment and strict improvement) `κ_HC(δ) ≤ M₂(δ)` and `κ_HC(δ) < κ_H(δ) = R_MQC(δ)`.
(iii) The combined exponent `κ_best := min{κ_CW, κ_HC}` satisfies
`R₂(δ) ≤ κ_best(δ) ≤ κ_bin(δ) ≤ R_2MQC(δ) < M₂(δ)` and `κ_best(δ) < R_2MQC(δ)`.

**Formalization Note.** `R₂` is the published `PrettyGoodCriterion.rateFunction` (codes in
`Fin n → Fin 2`, base-2 logarithm, real `lim sup`). `κ_HC` is Definition 1.1, `κ_H` is (55),
`κ_CW` is §6.5 (80), `M₂` is (2), `κ_bin = min{κ_H, κ_CW}`, and `R_MQC`, `R_2MQC` are the
normalized displays (119) and (124) of App. D. Every exponent is a real `sInf` of its printed
feasible set (strict spectral constraints as printed). -/
theorem theorem_1_2 (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    PrettyGoodCriterion.rateFunction δ ≤ kappaHC δ ∧
    (kappaHC δ ≤ M2 δ ∧ kappaHC δ < kappaH δ ∧ kappaH δ = RMQC δ) ∧
    (PrettyGoodCriterion.rateFunction δ ≤ kappaBest δ ∧ kappaBest δ ≤ kappaBin δ ∧
      kappaBin δ ≤ R2MQC δ ∧ R2MQC δ < M2 δ ∧ kappaBest δ < R2MQC δ) := by sorry

end HoneycombCodes
