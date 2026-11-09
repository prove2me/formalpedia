-- Prove2me | Theorems.Thm_IntervalMaxCutEPTAS_Scheme_lemma_4_6
-- name    : IntervalMaxCutEPTAS.Scheme.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:27.980628+00:00
-- url     : https://prove2.me/theorems/924e562f-77dc-4d3a-8fd3-677ed78fc7b0
-- title:
--   Lemma 4.6 — groups per anchor
-- statement:
--   Let $b\ge4$, $\sigma=2^{-b}$ and $\theta\in\{0,\dots,2M-1\}$. Every cell is the anchor of at most
--
--   $$(b+1)\,(2/\sigma+1)^2$$
--
--   groups.
--
--   Differences from the source:
--   - generalization: the shift θ fixed as in Lemma 4.2 (PDF p. 16) → every shift θ ∈ {0, …, 2M − 1}; reason: the source's proof of this item never uses Lemma 4.2's bound; specializing θ to the fixed shift gives the source statement
--   - encoding: vertex set V(G) of size n → Fin n, with a rank representation ρ (fields l, r, injectivity, range 1..2n, l < r); reason: labelling the vertices 0..n−1 restricts no instance; the structure is exactly §4.1's representation
--   - encoding: cells as open intervals (ζ, ζ + D) of a binary tree → cells named by heap indices 1 ≤ C < 8M with explicit cellLo, cellLen; groups named by their least vertex; reason: a bijective naming of the same cells and groups; geometry recomputed from the index
--   - encoding: (2/σ + 1)² → (2^{b+1} + 1)²; reason: exact value, σ = 2^{-b}
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), Lemma 4.6, PDF p. 17 (printed p. 16)

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Hierarchy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntervalMaxCutEPTAS.Scheme

/-- Lemma 4.6: every cell is the anchor of at most `(b + 1)(2/σ + 1)²` groups. -/
theorem lemma_4_6 {n : ℕ} (P : Setup n) (hb : 4 ≤ P.b) (hθ : P.θ < 2 * bigM n)
    (C : ℕ) (hC : IsCell n C) :
    (own P C).card ≤ (P.b + 1) * (2 ^ (P.b + 1) + 1) ^ 2 := by sorry

end IntervalMaxCutEPTAS.Scheme
