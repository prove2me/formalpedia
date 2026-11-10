-- Prove2me | Theorems.Thm_HoneycombCodes_theorem_5_5
-- name    : HoneycombCodes.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:30:42.363825+00:00
-- url     : https://prove2.me/theorems/84a7af31-aafe-4c8f-83ae-74dc241836fc
-- title:
--   Theorem 5.5 — soundness: $R_2(\delta)\le\kappa_{HC}(\delta)$
-- statement:
--   For every $0<\delta<1/2$,
--
--   $$
--   R_2(\delta)\le\kappa_{HC}(\delta),
--   $$
--
--   where $R_2(\delta)=\limsup_n\frac1n\log_2A_2(n,\lceil\delta n\rceil)$ is the asymptotic rate of binary codes of relative distance $\delta$ and $\kappa_{HC}$ is the first honeycomb exponent (Definition 1.1). This is part (i) of the main theorem.
--
--   Differences from the source:
--
--   - encoding: binary codes C ⊆ {±1}ⁿ and R₂(δ) = lim sup (1/n) log₂ A₂(n, ⌈δn⌉) → the published PrettyGoodCriterion.rateFunction (codes as Finsets of words Fin n → Fin 2, Real.logb 2, real Filter.limsup); reason: {±1} and Fin 2 are in bijection and Hamming distance is preserved; the sequence lies in [0, 1], so the real lim sup is the true one
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §5.2, Theorem 5.5, p.27 (PDF 29)

import Mathlib
import Definitions.Def_HoneycombCodes_kappaHC
import Definitions.Def_PrettyGoodCriterion_rateFunction

set_option autoImplicit false

namespace HoneycombCodes

/-- **Theorem 5.5**, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), p.27 (PDF 29). For every `0 < δ < 1/2`, `R₂(δ) ≤ κ_HC(δ)`.

**Formalization Note.** `R₂` is the published `PrettyGoodCriterion.rateFunction`
(`lim sup (1/n) log₂ A₂(n, ⌈δn⌉)`, codes in `Fin n → Fin 2`). -/
theorem theorem_5_5 (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    PrettyGoodCriterion.rateFunction δ ≤ kappaHC δ := by sorry

end HoneycombCodes
