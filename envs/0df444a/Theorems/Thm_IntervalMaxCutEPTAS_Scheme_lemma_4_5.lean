-- Prove2me | Theorems.Thm_IntervalMaxCutEPTAS_Scheme_lemma_4_5
-- name    : IntervalMaxCutEPTAS.Scheme.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:17:58.693208+00:00
-- url     : https://prove2.me/theorems/8982210a-24d5-48be-83f2-24ad5bbcc28c
-- title:
--   Lemma 4.5 — anchors
-- statement:
--   Let $b\ge4$, $\sigma=2^{-b}$, $\theta\in\{0,\dots,2M-1\}$, and let $v$ be a retained vertex whose anchor has length $D$.
--
--   1. $I_v\subseteq\mathrm{anc}(v)$, and $I_v$ contains the midpoint of $\mathrm{anc}(v)$; in particular $D\ge2$.
--   2. $\sigma D\le s_v<2D$, and $h_v\ge\max\{1,\sigma^2D\}$.
--   3. If $u$ is a retained vertex and $\mathrm{anc}(u)$, $\mathrm{anc}(v)$ are incomparable, then $I_u\cap I_v=\emptyset$. Hence every edge of $H$ joins two vertices with comparable anchors.
--
--   Differences from the source:
--   - generalization: the shift θ fixed as in Lemma 4.2 (PDF p. 16) → every shift θ ∈ {0, …, 2M − 1}; reason: the source's proof of this item never uses Lemma 4.2's bound; specializing θ to the fixed shift gives the source statement
--   - encoding: vertex set V(G) of size n → Fin n, with a rank representation ρ (fields l, r, injectivity, range 1..2n, l < r); reason: labelling the vertices 0..n−1 restricts no instance; the structure is exactly §4.1's representation
--   - encoding: cells as open intervals (ζ, ζ + D) of a binary tree → cells named by heap indices 1 ≤ C < 8M with explicit cellLo, cellLen; groups named by their least vertex; reason: a bijective naming of the same cells and groups; geometry recomputed from the index
--   - encoding: σ = 2^{-b} in inequalities → inequalities multiplied out by powers of two in ℕ/ℤ; reason: exact equivalence: σ is an exact power of two, nothing is rounded
--   - encoding: A_v ≤ ζ + D/2 ≤ B_v (midpoint) → 2A_v ≤ 2ζ + D ≤ 2B_v in ℤ; reason: exact equivalence
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), Lemma 4.5, PDF p. 17 (printed p. 16)

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Hierarchy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntervalMaxCutEPTAS.Scheme

/-- Lemma 4.5: for a retained `v` whose anchor `C` has length `D`, (a) `I_v ⊆ C`, `I_v` contains
the midpoint `ζ + D/2` of `C`, and `D ≥ 2`; (b) `σD ≤ s_v < 2D` and `h_v ≥ max{1, σ²D}`;
(c) a retained `u` whose anchor is incomparable with that of `v` has `I_u ∩ I_v = ∅`, hence every
edge of `H` joins two vertices with comparable anchors. -/
theorem lemma_4_5 {n : ℕ} (P : Setup n) (hb : 4 ≤ P.b) (hθ : P.θ < 2 * bigM n)
    (v : Fin n) (hv : ¬ Rejected P v) :
    (CellContains n (anchor P v) (A P v) (B P v) ∧
      2 * A P v ≤ 2 * cellLo n (anchor P v) + cellLen n (anchor P v) ∧
      2 * cellLo n (anchor P v) + cellLen n (anchor P v) ≤ 2 * B P v ∧
      2 ≤ cellLen n (anchor P v)) ∧
    (cellLen n (anchor P v) ≤ scale P v * 2 ^ P.b ∧ scale P v < 2 * cellLen n (anchor P v) ∧
      1 ≤ roundUnit P v ∧ cellLen n (anchor P v) ≤ roundUnit P v * 2 ^ (2 * P.b)) ∧
    ((∀ u, ¬ Rejected P u → ¬ Comparable (anchor P u) (anchor P v) →
        ¬ (max (A P u) (A P v) ≤ min (B P u) (B P v))) ∧
      ∀ u w, (H P).Adj u w → Comparable (anchor P u) (anchor P w)) := by sorry

end IntervalMaxCutEPTAS.Scheme
