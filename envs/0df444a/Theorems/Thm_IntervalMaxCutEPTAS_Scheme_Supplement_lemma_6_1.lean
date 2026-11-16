-- Prove2me | Theorems.Thm_IntervalMaxCutEPTAS_Scheme_Supplement_lemma_6_1
-- name    : IntervalMaxCutEPTAS.Scheme.Supplement.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:31:11.03288+00:00
-- url     : https://prove2.me/theorems/6a9cfe88-132e-4c7a-baad-e987001bba16
-- title:
--   Lemma 6.1 (used in the proof of Theorem 1.2) — ancestral endpoint spacing
-- statement:
--   Fix the rank representation and good-shift hierarchy of Proposition 4.10, with $b\ge4$ and $\sigma=2^{-b}$. For every nonroot cell $C$ of length $D$, every group $g$ anchored at a proper ancestor of $C$, and every endpoint $\xi$ of its interval strictly inside $C$,
--
--   $$h_g\ge\max\{1,2\sigma^2D\},\qquad h_g>\sigma d_C(\xi)/2.$$
--
--   Independently of whether such a group exists, the distinct ancestral positions satisfy
--
--   $$|P(C)|\le10b/\sigma.$$
--
--   This controls the number of boundary comparisons needed to determine an external neighborhood.
--
--   Differences from the source:
--   - encoding: the structure fixed in Proposition 4.10 with b ≥ 4 and its good shift → the published Setup, valid heap cell indices, group representative ids and GoodShift; reason: these are the same constructed objects and standing assumptions; no geometric or density condition is added
--   - encoding: integer positions in an open real cell and h_g inequalities → finite sets of integer positions; distance and inequalities in ℝ; σ as an exact integer power; reason: distinct positions are counted once and all source inequalities are unchanged
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), Lemma 6.1, PDF p. 23 (printed p. 22)

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Supplement_Endpoints

set_option autoImplicit false

namespace IntervalMaxCutEPTAS.Scheme.Supplement

/-- Lemma 6.1, PDF 23 (printed 22). The position bound does not require a group to exist. -/
theorem lemma_6_1 {n : ℕ} (P : Setup n) (hb : 4 ≤ P.b)
    (hθ : P.θ < 2 * bigM n) (hshift : GoodShift P)
    (C : ℕ) (hC : IsCell n C) (hroot : C ≠ 1) :
    (∀ g ∈ groups P, IsProperAncestor (anchor P g) C →
      ∀ ξ ∈ ancestralPositions P C, (ξ = A P g ∨ ξ = B P g) →
        (roundUnit P g : ℝ) ≥ max 1 (2 * sigma P.b ^ 2 * cellLen n C) ∧
        (roundUnit P g : ℝ) > sigma P.b * boundaryDistance n C ξ / 2) ∧
    ((ancestralPositions P C).card : ℝ) ≤ 10 * P.b / sigma P.b := by sorry

end IntervalMaxCutEPTAS.Scheme.Supplement
