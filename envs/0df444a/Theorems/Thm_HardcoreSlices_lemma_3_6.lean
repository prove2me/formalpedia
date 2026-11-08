-- Prove2me | Theorems.Thm_HardcoreSlices_lemma_3_6
-- name    : HardcoreSlices.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:37:07.290702+00:00
-- url     : https://prove2.me/theorems/01fcd184-381e-4cfe-b9db-7c8af79fbd39
-- title:
--   Lemma 3.6 — stronger expansion above $|X|/\Delta^a$
-- statement:
--   For all $0<a,b<1$ there is $\Delta_0$ such that for every $\Delta\ge\Delta_0$, with high probability over a random $\Delta$-regular bipartite graph, every $\tau$ in either side with $|\tau|\ge|X|/\Delta^a$ satisfies
--   $$|Y\setminus N(\tau)|<\frac{|Y|}{\Delta^b}.$$
--   This supplies the bound (11) on $(1+\lambda)^{\Delta_\tau}$ for large $|\tau|$ in the proof of Theorem 1.9.
--
--   Differences from the source:
--   - reading: there exists large enough ∆ → every ∆ ≥ Δ₀; reason: the use on p.23 needs every large ∆, and the proof gives it
--   - generalization: τ ⊆ X → τ in either side; reason: the model is symmetric in the two sides; the source is the case of side X
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), Lemma 3.6, p.16

import Mathlib
import Definitions.Def_HardcoreSlices_IsThreshold

open Classical

namespace HardcoreSlices

open ExpanderBIS.RandomHardCore

/-- **Lemma 3.6.** Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), p.16: "For all `0 < a, b < 1`, there exists large enough `∆` such that the following holds: for any random
`∆`-regular bipartite `G = (X, Y, E)`, with high probability over the randomness of `G`, every `τ ⊆ X` of size `|τ| ≥ |X|/∆^a` satisfies
`|Y \ N(τ)| < |Y|/∆^b`."

**Formalization Note.** "Large enough `∆`" is every `∆ ≥ Δ₀`, as its use on p.23 needs. Both sides are stated, as "(resp. `Y`)" of p.12 and its use
on `τ` of either side require. -/
theorem lemma_3_6 (a b : ℝ) (ha : 0 < a) (ha' : a < 1) (hb : 0 < b) (hb' : b < 1) :
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → AlmostEvery Δ (fun m G =>
      ∀ side ∈ ({oddSide m, evenSide m} : Finset (Finset (Vertex m))), ∀ τ ⊆ side,
        (m : ℝ) / (Δ : ℝ) ^ a ≤ τ.card →
          ((nonNbrs G side τ).card : ℝ) < (m : ℝ) / (Δ : ℝ) ^ b) := by sorry

end HardcoreSlices
