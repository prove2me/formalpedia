-- Prove2me | Theorems.Thm_HoneycombCodes_Supplement_theorem_9_3
-- name    : HoneycombCodes.Supplement.theorem_9_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:39:32.877189+00:00
-- url     : https://prove2.me/theorems/86628b75-8740-49e0-ad93-07e1227025dc
-- title:
--   Theorem 9.3 — unconditional Horn–channel bound $R_2\le\kappa^{[r]}_{ch}$, monotonicity, and the strict infimum is a closed minimum
-- statement:
--   For every $r\ge0$ and $0<\delta<1/2$,
--
--   $$
--   R_2(\delta)\le\kappa^{[r]}_{ch}(\delta),\qquad \kappa^{[r+1]}_{ch}(\delta)\le\kappa^{[r]}_{ch}(\delta).
--   $$
--
--   Moreover, the strict-constraint infimum defining $\kappa^{[r]}_{ch}(\delta)$ equals the minimum over the compact closed region $\Gamma_{ch}\ge1-2\delta$: there is $(K,L)\in\mathcal K_{r+1}$ with $\Gamma_{ch}(K,L)\ge1-2\delta$ and $\Phi_{ch}(K,L)=\kappa^{[r]}_{ch}(\delta)$, and $\kappa^{[r]}_{ch}(\delta)\le\Phi_{ch}(K,L)$ for every $(K,L)\in\mathcal K_{r+1}$ with $\Gamma_{ch}(K,L)\ge1-2\delta$.
--
--   Here $R_2(\delta)=\limsup_n\frac1n\log_2A_2(n,\lceil\delta n\rceil)$ and $\kappa^{[r]}_{ch}$ is the Horn–channel exponent (Definition 9.2). Every level of the hierarchy is an unconditional upper bound on the rate of binary codes.
--
--   Differences from the source:
--
--   - encoding: $R_2$ over binary codes in $\{\pm1\}^n$ → the published `PrettyGoodCriterion.rateFunction` (words `Fin n → Fin 2`, real `limsup`); reason: $\{\pm1\}$ and $\{0,1\}$ are in bijection preserving Hamming distance, and the sequence lies in $[0,1]$
--   - encoding: "the strict-constraint infimum equals the minimum over the closed region" → a minimizer exists in the closed region with value $\kappa^{[r]}_{ch}(\delta)$, and $\kappa^{[r]}_{ch}(\delta)$ is a lower bound on the closed region; reason: this is what equality with an attained minimum means
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §9, Theorem 9.3, eqs. (104)–(105), p.43 (PDF 45)

import Mathlib
import Definitions.Def_PrettyGoodCriterion_rateFunction
import Definitions.Def_HoneycombCodes_Supplement_kappaCh

set_option autoImplicit false

namespace HoneycombCodes.Supplement

/-- **Theorem 9.3**, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*,
arXiv:2608.20287v2 (sha256 f4b07e31…cd51), p.43 (PDF 45). For every `r ≥ 0` and `0 < δ < 1/2`,
`R₂(δ) ≤ κ^{[r]}_ch(δ)` (104) and `κ^{[r+1]}_ch(δ) ≤ κ^{[r]}_ch(δ)` (105); moreover the
strict-constraint infimum (103) equals the minimum over the compact closed region
`Γ_ch ≥ 1 − 2δ`: some `(K, L) ∈ K_{r+1}` with `Γ_ch(K, L) ≥ 1 − 2δ` has `Φ_ch(K, L) = κ^{[r]}_ch(δ)`,
and `κ^{[r]}_ch(δ) ≤ Φ_ch(K, L)` for every `(K, L) ∈ K_{r+1}` with `Γ_ch(K, L) ≥ 1 − 2δ`.

**Formalization Note.** `R₂` is the published `PrettyGoodCriterion.rateFunction`; `κ^{[r]}_ch` is
`kappaCh r` (matrices of size `r + 1`). -/
theorem theorem_9_3 (r : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    PrettyGoodCriterion.rateFunction δ ≤ kappaCh r δ ∧
      kappaCh (r + 1) δ ≤ kappaCh r δ ∧
      (∃ K L : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, InKset (r + 1) K L ∧
        1 - 2 * δ ≤ GammaCh K L ∧ PhiCh K L = kappaCh r δ) ∧
      ∀ K L : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, InKset (r + 1) K L →
        1 - 2 * δ ≤ GammaCh K L → kappaCh r δ ≤ PhiCh K L := by sorry

end HoneycombCodes.Supplement
