-- Prove2me | Theorems.Thm_IntervalMaxCutEPTAS_Scheme_lemma_4_7
-- name    : IntervalMaxCutEPTAS.Scheme.lemma_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:20.553849+00:00
-- url     : https://prove2.me/theorems/e84b6812-8e02-4bc8-89c2-0ba8ed28cbe2
-- title:
--   Lemma 4.7 — old groups act uniformly
-- statement:
--   Let $b\ge4$, $\theta\in\{0,\dots,2M-1\}$, $C$ a cell and $g\in O(C)$. Then $I_g$ contains the closure of $C$, and every vertex of $g$ is adjacent in $H$ to every vertex of $V_C$.
--
--   Differences from the source:
--   - generalization: the shift θ fixed as in Lemma 4.2 (PDF p. 16) → every shift θ ∈ {0, …, 2M − 1}; reason: the source's proof of this item never uses Lemma 4.2's bound; specializing θ to the fixed shift gives the source statement
--   - encoding: vertex set V(G) of size n → Fin n, with a rank representation ρ (fields l, r, injectivity, range 1..2n, l < r); reason: labelling the vertices 0..n−1 restricts no instance; the structure is exactly §4.1's representation
--   - encoding: cells as open intervals (ζ, ζ + D) of a binary tree → cells named by heap indices 1 ≤ C < 8M with explicit cellLo, cellLen; groups named by their least vertex; reason: a bijective naming of the same cells and groups; geometry recomputed from the index
--   - encoding: I_g ⊇ closure of C = [ζ, ζ + |C|] → A_g ≤ ζ and ζ + |C| ≤ B_g; reason: exact equivalence for closed intervals
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), Lemma 4.7, PDF p. 18 (printed p. 17)

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Hierarchy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntervalMaxCutEPTAS.Scheme

/-- Lemma 4.7: if `g ∈ O(C)`, then `I_g` contains the closure of `C`, and every vertex of `g` is
adjacent in `H` to every vertex of `V_C`. -/
theorem lemma_4_7 {n : ℕ} (P : Setup n) (hb : 4 ≤ P.b) (hθ : P.θ < 2 * bigM n)
    (C : ℕ) (hC : IsCell n C) (g : Fin n) (hg : g ∈ old P C) :
    A P g ≤ cellLo n C ∧ cellHi n C ≤ B P g ∧
      ∀ u ∈ groupOf P g, ∀ v ∈ VC P C, (H P).Adj u v := by sorry

end IntervalMaxCutEPTAS.Scheme
