-- Prove2me | Theorems.Thm_HardcoreSlices_lemma_3_11
-- name    : HardcoreSlices.lemma_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:37:33.415761+00:00
-- url     : https://prove2.me/theorems/86ddbe6a-2b29-44ed-918d-08bf848d44f1
-- title:
--   Lemma 3.11 — independent sets are rarely large on both sides
-- statement:
--   Let $\gamma$ be a threshold at $\ell=6$. There is $c>0$ such that for all large $\Delta$, with high probability over a random $\Delta$-regular bipartite graph $G$, for every $\lambda\in(0,c/\sqrt\Delta]$ and every $\alpha\ge(1-\gamma)\alpha^*(\Delta)$,
--   $$\Pr_{I\sim\mu_\lambda}\bigl[|I\cap X|>\alpha|X|,\ |I\cap Y|>\alpha|Y|\bigr]\le\exp\Bigl(-\frac{|X|}\Delta\Bigr).$$
--   It bounds the part of $Z_G(\lambda)$ that lies in the class medium on both sides, in Proposition 6.3.
--
--   Differences from the source:
--   - reading: γ = o∆(1) "fixed globally" (p.19) → every sequence γ with IsThreshold 6 γ; reason: the regimes share one γ (p.4) and p.20 sets ℓ ≥ 6; separate existentials would lose the overlap
--   - generalization: λ and α not ordered against the event → λ and α inside the event, uniformly; reason: the proof assumes only Lemma 3.1 for the graph; fixed λ, α follow by specialization
--   - reading: the sentence states no condition on ∆ → every ∆ ≥ Δ₀ for some Δ₀; reason: the paper's regime is ∆ large but fixed (p.2); γ = o∆(1) and α∗(∆) only make sense asymptotically in ∆ (p.3), and the proof takes ∆ large
--   - encoding: λ ≲ 1/√∆ for sufficiently small constant → 0 < λ ≤ c/√Δ with c > 0 chosen first; reason: the meaning of ≲ fixed on p.2
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), Lemma 3.11 (Lemma 1.12 restated), p.18

import Mathlib
import Definitions.Def_HardcoreSlices_IsThreshold
import Definitions.Def_HardcoreSlices_hcLaw

open Classical

namespace HardcoreSlices

open ExpanderBIS.RandomHardCore

/-- **Lemma 3.11 (Lemma 1.12 restated).** Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), p.18: "Let `G = (X, Y, E)` be a random `∆`-regular bipartite graph and `µλ` the corresponding hardcore model at fugacity `λ ≲ 1/√∆` for
sufficiently small constant. Then with high probability over the randomness in `G`, `Pr_{I∼µλ}[ |I ∩ X| > α|X|, |I ∩ Y| > α|Y| ] ≤ exp(−|X|/∆)`, when `α ≥ (1 − γ)α∗(∆)`."

**Formalization Note.** `γ` as in Theorem 1.8. `λ` and `α` are quantified inside the event, since the proof assumes only Lemma 3.1 for the graph. -/
theorem lemma_3_11 (γ : ℕ → ℝ) (hγ : IsThreshold 6 γ) :
    ∃ c : ℝ, 0 < c ∧ ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → AlmostEvery Δ (fun m G =>
      ∀ lam : ℝ, 0 < lam → lam ≤ c / Real.sqrt Δ → ∀ α : ℝ, (1 - γ Δ) * alphaStar Δ ≤ α →
        ∑ I ∈ (Finset.univ : Finset (Finset (Vertex m))).filter
            (fun I => α * m < (I ∩ oddSide m).card ∧ α * m < (I ∩ evenSide m).card), hcLaw G lam I ≤
          Real.exp (-((m : ℝ) / Δ))) := by sorry

end HardcoreSlices
