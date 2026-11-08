-- Prove2me | Theorems.Thm_HardcoreSlices_theorem_1_8
-- name    : HardcoreSlices.theorem_1_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:38:37.958203+00:00
-- url     : https://prove2.me/theorems/1ba61ac8-0e6c-48af-8659-e7f757e77d63
-- title:
--   Theorem 1.8 — the two-sided slice is a top-link expander below $(1-\gamma)\alpha^*(\Delta)$
-- statement:
--   Let $\gamma$ be a threshold at $\ell=6$. For all large $\Delta$ there is a polynomial such that with high probability over a random $\Delta$-regular bipartite graph $G$, for all $k_X,k_Y\le(1-\gamma)\alpha^*(\Delta)|X|$ with $k_X+k_Y\ge1$:
--
--   1. the slice $\mathcal I_{k_X,k_Y}(G)$ is nonempty;
--   2. the two-sided slice is a connected $\frac1{2(k_X+k_Y)}$-top-link spectral expander;
--   3. the down-up walk from any facet is within total variation $\varepsilon$ of $\mu^{(k_X,k_Y)}$ at every time $t\ge K(|X|+1+\log(1/\varepsilon))^r$, for all $\varepsilon\in(0,1)$.
--
--   The constants $K,r$ depend only on $\Delta$. This is the first of the paper's two main technical results.
--
--   Differences from the source:
--   - reading: γ = o∆(1) "fixed globally" (p.19) → every sequence γ with IsThreshold 6 γ; reason: the regimes share one γ (p.4) and p.20 sets ℓ ≥ 6; separate existentials would lose the overlap
--   - reading: mixes in polynomial-time → K (m + 1 + log 1/ε)^r with K, r chosen for each ∆, before m and G; reason: ∆ is large but fixed (p.2), and Theorem 1.2 gives this form
--   - reading: kX, kY ≤ α|X| → also 1 ≤ kX + kY; reason: at kX + kY = 0 the bound 1/(2·0) and the walk have no meaning
--   - generalization: the expander claim for the slice → also the conclusion that the slice is nonempty; reason: the proof of p.20 gives it, and it keeps µ a real distribution; the source is the other clauses
--   - reading: the sentence states no condition on ∆ → every ∆ ≥ Δ₀ for some Δ₀; reason: the paper's regime is ∆ large but fixed (p.2); γ = o∆(1) and α∗(∆) only make sense asymptotically in ∆ (p.3), and the proof takes ∆ large
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), Theorem 1.8, p.4

import Mathlib
import Definitions.Def_HardcoreSlices_IsThreshold
import Definitions.Def_HardcoreSlices_twoSidedSlice
import Definitions.Def_HDXConc_IsTopLinkExpander

open Classical

namespace HardcoreSlices

open ExpanderBIS.RandomHardCore

/-- **Theorem 1.8.** Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), p.4: "Let `G = (X, Y, E)` be a random `∆`-regular bipartite graph. Then with high probability over the randomness of `G`, the
two-sided independent set slice `(X, µ(kX,kY))` for `kX, kY ≤ α|X|` with `α = (1 − γ)α∗(∆)` fixed above is a connected `1/(2(kX+kY))`-top-link spectral
expander, and as a result, the down-up walk mixes in polynomial-time."

**Formalization Note.** The `γ` is any sequence with `IsThreshold 6 γ`, the paper's globally fixed one (p.19). The polynomial is chosen before `m` and `G`,
and depends on `∆`. The event quantifies over all `kX, kY`. `kX + kY = 0` is excluded, as `1/(2·0)` and a `0`-dimensional walk mean nothing.
The slice is nonempty in this range, so `µ^{(kX,kY)}` is a real distribution. -/
theorem theorem_1_8 (γ : ℕ → ℝ) (hγ : IsThreshold 6 γ) :
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∃ K r : ℕ, AlmostEvery Δ (fun m G =>
      ∀ kX kY : ℕ, 1 ≤ kX + kY →
        (kX : ℝ) ≤ (1 - γ Δ) * alphaStar Δ * m → (kY : ℝ) ≤ (1 - γ Δ) * alphaStar Δ * m →
        (twoSidedFacets G kX kY).Nonempty ∧
        HDXConc.IsTopLinkExpander (twoSidedComplex G kX kY) (kX + kY) (twoSidedLaw G kX kY)
          (1 / (2 * ((kX : ℝ) + kY))) ∧
        MixesInPoly (twoSidedComplex G kX kY) (kX + kY) (twoSidedLaw G kX kY) K r m) := by sorry

end HardcoreSlices
