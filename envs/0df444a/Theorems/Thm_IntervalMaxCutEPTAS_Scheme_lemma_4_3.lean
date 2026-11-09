-- Prove2me | Theorems.Thm_IntervalMaxCutEPTAS_Scheme_lemma_4_3
-- name    : IntervalMaxCutEPTAS.Scheme.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:24.720684+00:00
-- url     : https://prove2.me/theorems/1b33e6f5-40e4-42e4-9578-26687516156f
-- title:
--   Lemma 4.3 — rounded intervals
-- statement:
--   Let $b\ge4$, $\sigma=2^{-b}$, let $\theta\in\{0,\dots,2M-1\}$ be a shift and work in shifted coordinates ($\ell_v-\theta$, $r_v-\theta$). Every retained vertex $v$ satisfies:
--
--   1. $\ell_v\le A_v<\ell_v+h_v$ and $r_v-h_v<B_v\le r_v$; if $h_v=1$ then $I_v=[\ell_v,r_v]$;
--   2. $s_v/2\le B_v-A_v<2s_v$, in particular $A_v<B_v$;
--   3. $I_v$ is contained in the home of $v$.
--
--   Differences from the source:
--   - generalization: the shift θ fixed as in Lemma 4.2 (PDF p. 16) → every shift θ ∈ {0, …, 2M − 1}; reason: the source's proof of this item never uses Lemma 4.2's bound; specializing θ to the fixed shift gives the source statement
--   - encoding: vertex set V(G) of size n → Fin n, with a rank representation ρ (fields l, r, injectivity, range 1..2n, l < r); reason: labelling the vertices 0..n−1 restricts no instance; the structure is exactly §4.1's representation
--   - encoding: cells as open intervals (ζ, ζ + D) of a binary tree → cells named by heap indices 1 ≤ C < 8M with explicit cellLo, cellLen; groups named by their least vertex; reason: a bijective naming of the same cells and groups; geometry recomputed from the index
--   - encoding: s_v/2 ≤ B_v − A_v → s_v ≤ 2(B_v − A_v) in ℤ; reason: exact equivalence
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), Lemma 4.3, PDF p. 16 (printed p. 15)

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Hierarchy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntervalMaxCutEPTAS.Scheme

/-- Lemma 4.3 (shifted coordinates, every shift `θ < 2M`): for a retained vertex `v`,
(a) `l_v ≤ A_v < l_v + h_v`, `r_v − h_v < B_v ≤ r_v`, and `I_v = [l_v, r_v]` if `h_v = 1`;
(b) `s_v/2 ≤ B_v − A_v < 2s_v`, so `A_v < B_v`; (c) `I_v` lies in the home of `v`. -/
theorem lemma_4_3 {n : ℕ} (P : Setup n) (hb : 4 ≤ P.b) (hθ : P.θ < 2 * bigM n)
    (v : Fin n) (hv : ¬ Rejected P v) :
    (sl P v ≤ A P v ∧ A P v < sl P v + roundUnit P v ∧
      sr P v - roundUnit P v < B P v ∧ B P v ≤ sr P v ∧
      (roundUnit P v = 1 → A P v = sl P v ∧ B P v = sr P v)) ∧
    ((scale P v : ℤ) ≤ 2 * (B P v - A P v) ∧ B P v - A P v < 2 * (scale P v : ℤ) ∧
      A P v < B P v) ∧
    CellContains n (home P v) (A P v) (B P v) := by sorry

end IntervalMaxCutEPTAS.Scheme
