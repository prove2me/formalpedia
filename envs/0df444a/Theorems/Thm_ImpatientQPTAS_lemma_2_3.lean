-- Prove2me | Theorems.Thm_ImpatientQPTAS_lemma_2_3
-- name    : ImpatientQPTAS.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:59:36.796254+00:00
-- url     : https://prove2.me/theorems/a2a27d45-a175-4eca-aa90-4e8b8ff931d0
-- title:
--   Lemma 2.3 — the effect of rounding rewards
-- statement:
--   Let $\epsilon\in(0,\tfrac14)$, and let $\tilde r$ be rewards with $0\le\tilde r_i\le r_i$ and $\tilde r_i\ge r_i/(1+\epsilon)-(\epsilon/n)\,r_{\max}$ for all $i$. For every adaptive service policy $S$,
--   $$
--   (1-\epsilon)\,R^{(r)}(S)-\epsilon\,R^{(r)}(S^*)\le R^{(\tilde r)}(S)\le R^{(r)}(S),
--   $$
--   where $R^{(r)}(S^*)$ is the optimal value. Moreover, from any start set $B$,
--   $$
--   (1-\epsilon)\,R^{(r)}_B(S)-\epsilon\,r_{\max}\le R^{(\tilde r)}_B(S)\le R^{(r)}_B(S).
--   $$
--
--   Rounding rewards therefore costs only a small multiple of $\epsilon$ of the optimum.
--
--   Differences from the source:
--   - generalization: r̃ is the rounding of §2.2 → r̃ is any vector in the band r_i/(1+ε) − (ε/n)·r_max ≤ r̃_i ≤ r_i, r̃_i ≥ 0; reason: rRound_band shows the rounding lies in the band, and the page's absolute grid does too
--   - generalization: the start state [n] → a second clause from every start set B, with r_max in place of the optimum; reason: the first clause is the printed statement; the second is what the program needs for sets of average customers
--   - encoding: R^(r)(S*) → the optimal value V r p [n]; reason: the verification file proves V is the maximum over policies
-- source:
--   Segev, Near-Optimal Adaptive Policies for Serving Stochastically Departing Customers, arXiv:2209.13878v1, Lemma 2.3, p.9; proof App. A.3

import Mathlib
import Definitions.Def_ImpatientQPTAS_Model

namespace ImpatientQPTAS

/-- Segev, arXiv:2209.13878v1, Lemma 2.3, p.9: for every adaptive service policy `S`,
`(1 − ε)·R^(r)(S) − ε·R^(r)(S*) ≤ R^(r̃)(S) ≤ R^(r)(S)`.

**Formalization Note.** The statement holds for every `r̃` in the band
`r_i/(1+ε) − (ε/n)·r_max ≤ r̃_i ≤ r_i`, `0 ≤ r̃_i`, which covers the page's rounding and the grid relative
to `r_max` (see `rRound_band`). `R^(r)(S*)` is the optimal value `V r p [n]`. The second clause is the same
bound from any start set `B`, with `r_max` for the optimum, which §2.2's proof gives on the way. -/
theorem lemma_2_3 {n : ℕ} (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 4) (I : Instance n)
    (hI : I.Standing) (rt : Fin n → ℝ) (hlo : ∀ i, 0 ≤ rt i) (hhi : ∀ i, rt i ≤ I.r i)
    (hband : ∀ i, I.r i / (1 + ε) - ε / (n : ℝ) * rmax I.r ≤ rt i) :
    (∀ S : Policy n, IsPolicy S →
      (1 - ε) * I.R S - ε * V I.r I.p Finset.univ ≤ (⟨rt, I.p⟩ : Instance n).R S ∧
        (⟨rt, I.p⟩ : Instance n).R S ≤ I.R S) ∧
    (∀ (S : Policy n) (B : Finset (Fin n)), IsPolicy S →
      (1 - ε) * I.Rfrom S B - ε * rmax I.r ≤ (⟨rt, I.p⟩ : Instance n).Rfrom S B ∧
        (⟨rt, I.p⟩ : Instance n).Rfrom S B ≤ I.Rfrom S B) := by sorry

end ImpatientQPTAS
