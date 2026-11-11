-- Prove2me | Theorems.Thm_OptTwoSrcExt_corollary_2_20
-- name    : OptTwoSrcExt.corollary_2_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:26:32.617597+00:00
-- url     : https://prove2.me/theorems/8e6df895-829a-4f08-af30-09a7f0d2da41
-- title:
--   Corollary 2.20 — linear-rank dispersion upgrade: low-rank dispersers extract with error $2^{-\eta n}$
-- statement:
--   Fix $A,\rho,\xi>0$ with $\rho+\xi\le1$. There is $\eta>0$ such that for every $n$, every Boolean function $h:\{0,1\}^n\times\{0,1\}^n\to\mathbb F_2$ that is a two-source disperser at side threshold $\rho n$ and has binary rank $\mathrm{rank}_2 h\le An$ is an ordinary two-source extractor at side entropy $(\rho+\xi)n$ with error $2^{-\eta n}$:
--   $$\Delta\big(h(X,Y),U_1\big)\le2^{-\eta n}\quad\text{for all independent } X,Y \text{ with } H_\infty(X),H_\infty(Y)\ge(\rho+\xi)n .$$
--   The exponent $\eta$ is uniform over all functions satisfying the two hypotheses.
--
--   This is the upgrade (Ben-Sasson–Ron-Zewi, with the polynomial Freiman–Ruzsa theorem of Gowers–Green–Manners–Tao) used in Corollary 3.32 and Theorem 3.33.
--
--   **Formalization Note** The statement is for every $n$, as printed. "Ordinary extractor" is the published `LowErrExt.IsTwoSourceExtractor`, over all probability mass functions.
--
--   Differences from the source:
--   - encoding: Boolean ρn-two-source disperser of rank at most An; ordinary extractor with error 2^{−ηn} → IsBoolDisperser (ρn) h with rank2 h ≤ An, h : {0,1}^n × {0,1}^n → ZMod 2; LowErrExt.IsTwoSourceExtractor ((ρ+ξ)n) (2^{−ηn}) h; reason: Lean convention; same instances
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Corollary 2.20, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_LowErrExt_IsTwoSourceExtractor
import Definitions.Def_OptTwoSrcExt_rank2
import Definitions.Def_OptTwoSrcExt_IsBoolDisperser

open LowErrExt

namespace OptTwoSrcExt

/-- **Corollary 2.20 (Linear-rank dispersion upgrade).**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Corollary 2.20, printed p.22 (PDF p.24): "For fixed A, ρ,
ξ > 0 with ρ + ξ ⩽ 1, there is η > 0 such that every Boolean ρn-two-source disperser of rank at most
An is an ordinary extractor at side entropy (ρ + ξ)n with error 2^{−ηn}. The exponent is uniform over
all functions satisfying these two hypotheses."

For fixed `A, ρ, ξ > 0` with `ρ + ξ ≤ 1` there is `η > 0` such that, for every `n` and every Boolean
function `h : {0,1}ⁿ × {0,1}ⁿ → 𝔽₂` that is a two-source disperser at side threshold `ρn` and has
`rank₂ h ≤ An`, the function `h` is a two-source extractor for min-entropy `(ρ + ξ)n` with error
`2^{−ηn}`: `Δ(h(X, Y), U₁) ≤ 2^{−ηn}` for all independent `X, Y` with `H∞ ≥ (ρ + ξ)n`.

**Formalization Note.** `η` is chosen before `n` and `h` (uniformity). The statement is for every
`n`, as printed (no "sufficiently large n" clause). "Ordinary extractor" is the published
`LowErrExt.IsTwoSourceExtractor` (all probability mass functions, not only flat sources); the
output `𝔽₂` is `ZMod 2`, whose uniform law is `U₁`. -/
theorem corollary_2_20 (A ρ ξ : ℝ) (hA : 0 < A) (hρ : 0 < ρ) (hξ : 0 < ξ) (hρξ : ρ + ξ ≤ 1) :
    ∃ η : ℝ, 0 < η ∧ ∀ (n : ℕ) (h : (Fin n → Bool) → (Fin n → Bool) → ZMod 2),
      IsBoolDisperser (ρ * n) h → (rank2 h : ℝ) ≤ A * n →
        IsTwoSourceExtractor ((ρ + ξ) * n) ((2 : ℝ) ^ (-(η * n))) h := by sorry

end OptTwoSrcExt
