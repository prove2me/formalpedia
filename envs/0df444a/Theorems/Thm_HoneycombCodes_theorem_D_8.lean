-- Prove2me | Theorems.Thm_HoneycombCodes_theorem_D_8
-- name    : HoneycombCodes.theorem_D_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:31:05.751212+00:00
-- url     : https://prove2.me/theorems/fdf035d2-4912-4ebb-b6e4-d7322a3ef31f
-- title:
--   Theorem D.8 — moving-projection bounds versus 2MQC
-- statement:
--   For every $0<\delta<1/2$,
--
--   $$
--   \kappa_{bin}(\delta)\le R_{2MQC}(\delta), \tag{136}
--   $$
--
--   $$
--   \kappa_{pair}(\delta)=\min\{\kappa_{CW}(\delta),\kappa_{bal}(\delta)\}<R_{2MQC}(\delta), \tag{137}
--   $$
--
--   and consequently
--
--   $$
--   R_2(\delta)\le\kappa_{best}(\delta)\le\kappa_{explicit}(\delta)\le\min\{\kappa_{bin}(\delta),\kappa_{pair}(\delta)\}<R_{2MQC}(\delta)<M_2(\delta). \tag{138}
--   $$
--
--   Differences from the source:
--
--   - encoding: binary codes C ⊆ {±1}ⁿ and R₂(δ) = lim sup (1/n) log₂ A₂(n, ⌈δn⌉) → the published PrettyGoodCriterion.rateFunction (codes as Finsets of words Fin n → Fin 2, Real.logb 2, real Filter.limsup); reason: {±1} and Fin 2 are in bijection and Hamming distance is preserved; the sequence lies in [0, 1], so the real lim sup is the true one
--   - reading: the MQC and 2MQC exponents of [AG26] (recalled in Appendix D) → R_MQC and R_2MQC defined by the paper's normalized displays (119) and (122)–(124), with λ_δ(0,0) = 2δ; reason: Theorem 1.2 refers to App. D for these exponents; the normalized displays are the only definitions this paper states
--   - encoding: κ_pair(δ) = min{κ_CW(δ), κ_bal(δ)} in (137) → the definition kappaPair; reason: the equality in (137) is the definition of κ_pair (p.29)
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), App. D.5, Theorem D.8, eqs. (136)–(138), p.65 (PDF 67)

import Mathlib
import Definitions.Def_HoneycombCodes_kappaHC
import Definitions.Def_HoneycombCodes_kappaBal
import Definitions.Def_HoneycombCodes_R2MQC
import Definitions.Def_HoneycombCodes_M2
import Definitions.Def_PrettyGoodCriterion_rateFunction

set_option autoImplicit false

namespace HoneycombCodes

/-- **Theorem D.8**, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), App. D.5, p.65 (PDF 67). For every `0 < δ < 1/2`,
`κ_bin(δ) ≤ R_2MQC(δ)` (136), `κ_pair(δ) = min{κ_CW(δ), κ_bal(δ)} < R_2MQC(δ)` (137), and
consequently
`R₂(δ) ≤ κ_best(δ) ≤ κ_explicit(δ) ≤ min{κ_bin(δ), κ_pair(δ)} < R_2MQC(δ) < M₂(δ)` (138).

**Formalization Note.** `κ_pair = min{κ_CW, κ_bal}` is the definition `kappaPair`; `R₂` is the
published `PrettyGoodCriterion.rateFunction`. -/
theorem theorem_D_8 (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    kappaBin δ ≤ R2MQC δ ∧
    kappaPair δ < R2MQC δ ∧
    (PrettyGoodCriterion.rateFunction δ ≤ kappaBest δ ∧ kappaBest δ ≤ kappaExplicit δ ∧
      kappaExplicit δ ≤ min (kappaBin δ) (kappaPair δ) ∧
      min (kappaBin δ) (kappaPair δ) < R2MQC δ ∧ R2MQC δ < M2 δ) := by sorry

end HoneycombCodes
