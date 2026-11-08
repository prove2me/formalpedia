-- Prove2me | Theorems.Thm_HardcoreSlices_lemma_3_1
-- name    : HardcoreSlices.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:37:09.370969+00:00
-- url     : https://prove2.me/theorems/a0dbb1c1-0ed9-451d-b083-7587e1ab0187
-- title:
--   Lemma 3.1 — expansion and anti-expansion of random regular bipartite graphs
-- statement:
--   Let $G=(X,Y,E)$ be a random $\Delta$-regular bipartite graph. For every $\ell>0$ there is a sequence $\gamma=o_\Delta(1)$ in $(0,1)$ for large $\Delta$ such that, for all large $\Delta$, with high probability, every $\tau\subseteq X$ (and every $\tau\subseteq Y$) satisfies:
--
--   1. (Expansion) if $|\tau|\ge(1-\gamma)\alpha^*(\Delta)|X|$ then $|Y\setminus N(\tau)|\le\frac{(\ell+1)\log\Delta}{\sqrt\Delta}|Y|$;
--   2. (Anti-expansion) if $|\tau|\le(1-\gamma)\alpha^*(\Delta)|X|$ then $|Y\setminus N(\tau)|\ge\frac{\ell\log\Delta}{\sqrt\Delta}|Y|$.
--
--   The two clauses locate the density threshold of the slices: enough free vertices to keep the two-sided slice expanding below it, and few enough to control the one-sided slice above it.
--
--   Differences from the source:
--   - encoding: there is γ = o∆(1) with the property for all large ∆ → IsThreshold ℓ γ; reason: the predicate packages exactly that; it also records 0 < γ < 1 for large ∆, which makes (1 − γ)α∗ a density
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), Lemma 3.1, pp.12–13

import Mathlib
import Definitions.Def_HardcoreSlices_IsThreshold

open Classical

namespace HardcoreSlices

/-- **Lemma 3.1.** Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), pp.12–13: "Let `G = (X, Y, E)` be a random `∆`-regular bipartite graph. For any `ℓ > 0` and all sufficiently large
`∆ > 0` large enough there is `γ = o∆(1)` such that with high probability over the randomness of `G` and in the size of the graph, every
`τ ⊆ X` (resp. `Y`) satisfies the following: 1. (Expansion) If `|τ| ≥ (1 − γ)α∗(∆)|X|` then `|Y \ N(τ)| ≤ ((ℓ + 1) log ∆ / √∆)|Y|`.
2. (Anti-expansion) If `|τ| ≤ (1 − γ)α∗(∆)|X|` then `|Y \ N(τ)| ≥ (ℓ log ∆ / √∆)|Y|`."

**Formalization Note.** `IsThreshold` packages the sequence `γ = o∆(1)` and the statement for all large `∆`. -/
theorem lemma_3_1 (ℓ : ℝ) (hℓ : 0 < ℓ) : ∃ γ : ℕ → ℝ, IsThreshold ℓ γ := by sorry

end HardcoreSlices
