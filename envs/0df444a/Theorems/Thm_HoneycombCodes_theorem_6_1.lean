-- Prove2me | Theorems.Thm_HoneycombCodes_theorem_6_1
-- name    : HoneycombCodes.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:30:44.545333+00:00
-- url     : https://prove2.me/theorems/6d33b96f-3fcd-48e5-a541-12011ddb0b41
-- title:
--   Theorem 6.1 — first honeycomb bound, full version
-- statement:
--   For every $0<\delta<1/2$,
--
--   $$
--   R_2(\delta)\le\kappa_{HC}(\delta),\qquad \kappa_{bal}(\delta)\le M_2(\delta),
--   $$
--
--   $$
--   \kappa_{HC}(\delta)\le\kappa_{face}(\delta)<\kappa_H(\delta),\qquad \kappa_{HC}(\delta)\le\kappa_{bal}(\delta)<\kappa_H(\delta),
--   $$
--
--   $$
--   R_2(\delta)\le\kappa_{best}(\delta)\le\kappa_{explicit}(\delta)\le\kappa_{bin}(\delta)\le R_{2MQC}(\delta)<M_2(\delta)\le M_1(\delta),
--   $$
--
--   $$
--   \kappa_{explicit}(\delta)\le\kappa_{pair}(\delta)<R_{2MQC}(\delta),\qquad \kappa_H(\delta)=R_{MQC}(\delta).
--   $$
--
--   Theorem 1.2 follows from it.
--
--   Differences from the source:
--
--   - encoding: binary codes C ⊆ {±1}ⁿ and R₂(δ) = lim sup (1/n) log₂ A₂(n, ⌈δn⌉) → the published PrettyGoodCriterion.rateFunction (codes as Finsets of words Fin n → Fin 2, Real.logb 2, real Filter.limsup); reason: {±1} and Fin 2 are in bijection and Hamming distance is preserved; the sequence lies in [0, 1], so the real lim sup is the true one
--   - reading: the MQC and 2MQC exponents of [AG26] (recalled in Appendix D) → R_MQC and R_2MQC defined by the paper's normalized displays (119) and (122)–(124), with λ_δ(0,0) = 2δ; reason: Theorem 1.2 refers to App. D for these exponents; the normalized displays are the only definitions this paper states
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §6.1, Theorem 6.1, p.29 (PDF 31)

import Mathlib
import Definitions.Def_HoneycombCodes_kappaHC
import Definitions.Def_HoneycombCodes_kappaBal
import Definitions.Def_HoneycombCodes_R2MQC
import Definitions.Def_HoneycombCodes_RMQC
import Definitions.Def_HoneycombCodes_M2
import Definitions.Def_PrettyGoodCriterion_rateFunction

set_option autoImplicit false

namespace HoneycombCodes

/-- **Theorem 6.1 (First honeycomb bound, full version)**, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), p.29 (PDF 31). For every
`0 < δ < 1/2`:
`R₂(δ) ≤ κ_HC(δ)`, `κ_bal(δ) ≤ M₂(δ)`; `κ_HC(δ) ≤ κ_face(δ) < κ_H(δ)`;
`κ_HC(δ) ≤ κ_bal(δ) < κ_H(δ)`;
`R₂(δ) ≤ κ_best(δ) ≤ κ_explicit(δ) ≤ κ_bin(δ) ≤ R_2MQC(δ) < M₂(δ) ≤ M₁(δ)`;
`κ_explicit(δ) ≤ κ_pair(δ) < R_2MQC(δ)`; `κ_H(δ) = R_MQC(δ)`.

**Formalization Note.** `R₂` is the published `PrettyGoodCriterion.rateFunction`; every other
exponent is the corresponding local definition (all chains written as conjunctions of their
links). -/
theorem theorem_6_1 (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    (PrettyGoodCriterion.rateFunction δ ≤ kappaHC δ ∧ kappaBal δ ≤ M2 δ) ∧
    (kappaHC δ ≤ kappaFace δ ∧ kappaFace δ < kappaH δ) ∧
    (kappaHC δ ≤ kappaBal δ ∧ kappaBal δ < kappaH δ) ∧
    (PrettyGoodCriterion.rateFunction δ ≤ kappaBest δ ∧ kappaBest δ ≤ kappaExplicit δ ∧
      kappaExplicit δ ≤ kappaBin δ ∧ kappaBin δ ≤ R2MQC δ ∧ R2MQC δ < M2 δ ∧ M2 δ ≤ M1 δ) ∧
    (kappaExplicit δ ≤ kappaPair δ ∧ kappaPair δ < R2MQC δ) ∧
    kappaH δ = RMQC δ := by sorry

end HoneycombCodes
