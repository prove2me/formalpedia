-- Prove2me | Theorems.Thm_HoneycombCodes_Supplement_theorem_1_3
-- name    : HoneycombCodes.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:36:47.674185+00:00
-- url     : https://prove2.me/theorems/d78b1da5-4be0-48d8-91b2-5c438239d18e
-- title:
--   Theorem 1.3 — Horn–channel hierarchy $R_2\le\kappa^{[r+1]}_{ch}\le\kappa^{[r]}_{ch}$, $\kappa^{[0]}_{ch}=M_1$, $\kappa^{[1]}_{ch}=\kappa_{HC}$, $\kappa^{[r]}_{ch}\to\mathfrak B_{PGM}$
-- statement:
--   For every $0<\delta<1/2$ and $r\ge0$:
--
--   1. $R_2(\delta)\le\kappa^{[r+1]}_{ch}(\delta)\le\kappa^{[r]}_{ch}(\delta)$;
--   2. $\kappa^{[0]}_{ch}(\delta)=M_1(\delta)$ and $\kappa^{[1]}_{ch}(\delta)=\kappa_{HC}(\delta)$;
--   3. $\displaystyle\lim_{r\to\infty}\kappa^{[r]}_{ch}(\delta)=\mathfrak B_{PGM}(\delta)$, the infimum of the uniform-prior Holevo information over all finite-dimensional binary classical–quantum channels whose PGM bit error is below $\delta$. More precisely, the uniform-prior Holevo information and PGM error of any channel on $\mathbb C^d$ are realized exactly at level $2d-1$: for every $d\ge1$ and all density matrices $\rho_0,\rho_1$ on $\mathbb C^d$ there is $(K,L)\in\mathcal K_{2d}$ with
--
--   $$
--   \Phi_{ch}(K,L)=\chi(\rho_0,\rho_1),\qquad \Gamma_{ch}(K,L)=1-2p_e(\rho_0,\rho_1).
--   $$
--
--   Here $R_2(\delta)=\limsup_n\frac1n\log_2A_2(n,\lceil\delta n\rceil)$, $M_1(\delta)=H_2(\tfrac12-\sqrt{\delta(1-\delta)})$ is the first MRRW exponent, $\kappa_{HC}$ the first honeycomb exponent, and $\kappa^{[r]}_{ch}$ the Horn–channel exponent at row level $r$ (matrices of size $r+1$). The hierarchy interpolates between the first MRRW bound, the first honeycomb bound and the limit of the pretty-good criterion of Alrabiah and Guruswami.
--
--   Differences from the source:
--
--   - encoding: $R_2$ over binary codes in $\{\pm1\}^n$ → the published `PrettyGoodCriterion.rateFunction` (codes as Finsets of words `Fin n → Fin 2`, real `limsup`); reason: $\{\pm1\}$ and $\{0,1\}$ are in bijection preserving Hamming distance, and the sequence lies in $[0,1]$
--   - encoding: $S(M)=-\operatorname{tr}(M\log_2M)$, $\chi$, $p_e$ → the published `QAlgorithms.vnEntropy`, `PrettyGoodCriterion.holevoUniform`, `PrettyGoodCriterion.pgmBitErrorUniform` (PGM error with inverses on the support); reason: the same quantities, $p_e$ equals the binary formula (140)
--   - encoding: $\lim_{r\to\infty}$ and the infima → `Filter.Tendsto` along `r` and real `sInf`s of nonempty sets bounded below; reason: Lean convention, same values
--   - encoding: "level $2d-1$" → matrices indexed by `Fin (2 * d)`; reason: level $r$ uses matrices of size $r+1$ (Definition 9.2)
--   - encoding: "$\kappa^{[0]}_{ch}=M_1$ and $\kappa^{[1]}_{ch}=\kappa_{HC}$" (as functions on $(0,1/2)$) → equality at each $\delta$ of the statement; reason: the statement is quantified over every $0<\delta<1/2$
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §1.2, Theorem 1.3, p.5 (PDF 7)

import Mathlib
import Definitions.Def_PrettyGoodCriterion_rateFunction
import Definitions.Def_HoneycombCodes_M2
import Definitions.Def_HoneycombCodes_kappaHC
import Definitions.Def_HoneycombCodes_Supplement_kappaCh

set_option autoImplicit false

open Filter Topology

namespace HoneycombCodes.Supplement

/-- **Theorem 1.3 (Horn–channel hierarchy)**, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework
for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), p.5 (PDF 7). For every `0 < δ < 1/2`
and `r ≥ 0`:
(a) `R₂(δ) ≤ κ^{[r+1]}_ch(δ) ≤ κ^{[r]}_ch(δ)`;
(b) `κ^{[0]}_ch = M₁` and `κ^{[1]}_ch = κ_HC`;
(c) `lim_{r→∞} κ^{[r]}_ch(δ) = B_PGM(δ)`; more precisely, the uniform-prior Holevo information and
PGM error of any channel on `ℂ^d` are realized exactly at level `2d − 1`: for every `d ≥ 1` and every
pair of density matrices `ρ₀, ρ₁` on `ℂ^d` there is `(K, L) ∈ K_{2d}` with `Φ_ch(K, L) = χ(ρ₀, ρ₁)`
and `Γ_ch(K, L) = 1 − 2 p_e(ρ₀, ρ₁)`.

**Formalization Note.** `M₁`, `κ_HC` are the published `HoneycombCodes.M1`,
`HoneycombCodes.kappaHC`; (b) is stated at the given `δ`. The limit is `Filter.Tendsto` along `r`.
Level `2d − 1` uses matrices of size `2d`. -/
theorem theorem_1_3 (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) (r : ℕ) :
    (PrettyGoodCriterion.rateFunction δ ≤ kappaCh (r + 1) δ ∧
        kappaCh (r + 1) δ ≤ kappaCh r δ) ∧
      (kappaCh 0 δ = HoneycombCodes.M1 δ ∧ kappaCh 1 δ = HoneycombCodes.kappaHC δ) ∧
      (Tendsto (fun r' : ℕ => kappaCh r' δ) atTop (𝓝 (BPGM δ)) ∧
        ∀ (d : ℕ), 1 ≤ d → ∀ ρ : Fin 2 → Matrix (Fin d) (Fin d) ℂ, (∀ b, IsDensity (ρ b)) →
          ∃ K L : Matrix (Fin (2 * d)) (Fin (2 * d)) ℂ, InKset (2 * d) K L ∧
            PhiCh K L = PrettyGoodCriterion.holevoUniform ρ ∧
            GammaCh K L = 1 - 2 * PrettyGoodCriterion.pgmBitErrorUniform ρ) := by sorry

end HoneycombCodes.Supplement
