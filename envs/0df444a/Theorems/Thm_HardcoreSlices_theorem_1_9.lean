-- Prove2me | Theorems.Thm_HardcoreSlices_theorem_1_9
-- name    : HardcoreSlices.theorem_1_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:39:37.971795+00:00
-- url     : https://prove2.me/theorems/470efa2e-c8d1-4ad4-89c2-d8d44183c403
-- title:
--   Theorem 1.9 — the one-sided slice is a top-link expander for $\alpha|X|\le k\le4\lambda|X|$
-- statement:
--   Let $\gamma$ be a threshold at $\ell=6$. There is $c>0$ such that for all large $\Delta$ there is a polynomial for which, with high probability over a random $\Delta$-regular bipartite graph $G$, for every $\lambda\in(0,c/\sqrt\Delta]$, each side, and every $k$ with $(1-\gamma)\alpha^*(\Delta)|X|\le k\le4\lambda|X|$:
--
--   1. the one-sided slice of the hardcore model is a connected $\frac1{2k}$-top-link spectral expander;
--   2. the down-up walk from any facet is within total variation $\varepsilon$ of $\mu_\lambda^{(k)}$ at every time $t\ge K(|X|+1+\log(1/\varepsilon))^r$, for all $\varepsilon\in(0,1)$.
--
--   The constants $K,r$ depend only on $\Delta$. Above the density where the two-sided slice stops expanding, this chain takes over.
--
--   Differences from the source:
--   - reading: γ = o∆(1) "fixed globally" (p.19) → every sequence γ with IsThreshold 6 γ; reason: the regimes share one γ (p.4) and p.20 sets ℓ ≥ 6; separate existentials would lose the overlap
--   - generalization: the sentence fixes no order between λ and the high-probability event → λ quantified inside the event, uniformly over its range; reason: the events the proof uses do not mention λ; a fixed-λ statement follows by specialization
--   - reading: mixes in polynomial-time → K (m + 1 + log 1/ε)^r with K, r chosen for each ∆, before m, G, λ; reason: log(1/µmin) ≤ O(m) on the slice, uniformly in λ, since k is fixed
--   - encoding: λ ≲ 1/√∆ → λ ≤ c/√∆ with c first; reason: the convention of p.2
--   - reading: the sentence states no condition on ∆ → every ∆ ≥ Δ₀ for some Δ₀; reason: the paper's regime is ∆ large but fixed (p.2); γ = o∆(1) and α∗(∆) only make sense asymptotically in ∆ (p.3), and the proof takes ∆ large
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), Theorem 1.9, p.4

import Mathlib
import Definitions.Def_HardcoreSlices_oneSidedSlice
import Definitions.Def_HDXConc_IsTopLinkExpander

open Classical

namespace HardcoreSlices

open ExpanderBIS.RandomHardCore

/-- **Theorem 1.9.** Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), p.4: "Let `G = (X, Y, E)` be a random `∆`-regular bipartite graph. Then with high probability over the randomness of `G`, the
one-sided slice of the hardcore model `(X, µλ^(k))` for `α|X| ≤ k ≤ β|X|` with `α = (1 − γ)α∗(∆)` fixed above and `β = 4λ` at fugacity `λ ≲ 1/√∆` is a connected
`1/(2k)`-top-link spectral expander, and as a result, the down-up walk mixes in polynomial-time."

**Formalization Note.** `γ` as in Theorem 1.8. `λ ≲ 1/√∆` is `λ ≤ c/√∆` (p.2), with `c` chosen before `∆`. `λ`, `k` and the side are quantified inside the high-probability event: the
events used by the proof do not mention `λ`. The polynomial depends on `∆`, not on `λ`. -/
theorem theorem_1_9 (γ : ℕ → ℝ) (hγ : IsThreshold 6 γ) :
    ∃ c : ℝ, 0 < c ∧ ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∃ K r : ℕ, AlmostEvery Δ (fun m G =>
      ∀ lam : ℝ, 0 < lam → lam ≤ c / Real.sqrt Δ → ∀ (b : Bool) (k : ℕ),
        (1 - γ Δ) * alphaStar Δ * m ≤ k → (k : ℝ) ≤ 4 * lam * m →
        HDXConc.IsTopLinkExpander (oneSidedComplex (sideOf m b) k) k (oneSidedLaw G lam (sideOf m b) k)
          (1 / (2 * (k : ℝ))) ∧
        MixesInPoly (oneSidedComplex (sideOf m b) k) k (oneSidedLaw G lam (sideOf m b) k) K r m) := by sorry

end HardcoreSlices
