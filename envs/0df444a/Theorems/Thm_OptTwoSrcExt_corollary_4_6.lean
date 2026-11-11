-- Prove2me | Theorems.Thm_OptTwoSrcExt_corollary_4_6
-- name    : OptTwoSrcExt.corollary_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:25:10.748586+00:00
-- url     : https://prove2.me/theorems/16ff93a8-52f6-45a9-9ea8-004bfa7b1c5f
-- title:
--   Corollary 4.6 — short-output strongification: source-strong error $2^d(\eta_0+2^{h-k})$
-- statement:
--   Let $E:\{0,1\}^n\times\{0,1\}^n\to\{0,1\}^d$ be an ordinary two-source extractor for min-entropy $h$ with error $\eta_0$, and let $k>h$. Then for all independent sources $X,Y$ with $H_\infty(X),H_\infty(Y)\ge k$,
--   $$\Delta\big((E(X,Y),Y),(U_d,Y)\big)\le 2^d\big(\eta_0+2^{h-k}\big)\quad\text{and}\quad \Delta\big((E(X,Y),X),(U_d,X)\big)\le 2^d\big(\eta_0+2^{h-k}\big),$$
--   with $U_d$ uniform and independent of the retained source.
--
--   Entropy slack thus buys source strength for a short output; in the proof of Theorem 1.5 it gives the seed's strength $\eta\le2^{d+1-a_*n}$ in (4.5).
--
--   **Formalization Note** "Strong in either original source" is Definition 2.3 with no tamperings, the two comparisons separately; this is the published `LowErrExt.IsStrongTwoSourceExtractor`.
--
--   Differences from the source:
--   - encoding: error strong in either original source (Definition 2.3 with t = 0) → LowErrExt.IsStrongTwoSourceExtractor: the comparisons retaining X and retaining Y, each with the bound; reason: Lean convention; same instances
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Corollary 4.6, p.85 (PDF p.87); Lemma 2.5, p.15; Definition 2.3, p.14

import Mathlib
import Definitions.Def_LowErrExt_IsTwoSourceExtractor

open LowErrExt

namespace OptTwoSrcExt

/-- **Corollary 4.6 (Short-output strongification).**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Corollary 4.6, printed p.85 (PDF p.87): "If an ordinary
d-bit two-source extractor works at component threshold h with error η0, then at component entropy
k > h its error strong in either original source is at most 2^d(η0 + 2^{h−k})."

If `E : {0,1}ⁿ × {0,1}ⁿ → {0,1}^d` is a two-source extractor for min-entropy `h` with error `η₀`, and
`k > h`, then for all independent `X, Y` with min-entropy at least `k`, both
`Δ((E(X, Y), Y), (U_d, Y))` and `Δ((E(X, Y), X), (U_d, X))` are at most `2^d(η₀ + 2^{h−k})`.

**Formalization Note.** "Strong in either original source" is Definition 2.3 (p.14) with `t = 0`: the
two comparisons retaining `X` or retaining `Y`, separately. This is exactly the published
`LowErrExt.IsStrongTwoSourceExtractor` (`U_d` uniform and independent of the retained source);
"ordinary two-source extractor" is the published `LowErrExt.IsTwoSourceExtractor`. Sources are
arbitrary probability mass functions and `h, k` are real. -/
theorem corollary_4_6 {n d : ℕ} (h k η₀ : ℝ)
    (E : (Fin n → Bool) → (Fin n → Bool) → (Fin d → Bool))
    (hE : IsTwoSourceExtractor h η₀ E) (hk : h < k) :
    IsStrongTwoSourceExtractor k ((2 : ℝ) ^ d * (η₀ + (2 : ℝ) ^ (h - k))) E := by sorry

end OptTwoSrcExt
