-- Prove2me | Theorems.Thm_IntervalMaxCutEPTAS_Scheme_lemma_4_8
-- name    : IntervalMaxCutEPTAS.Scheme.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:10.971949+00:00
-- url     : https://prove2.me/theorems/678dae3c-e96a-4bc8-9525-dca7ca240d96
-- title:
--   Lemma 4.8 — external neighbours
-- statement:
--   Let $b\ge4$, $\theta\in\{0,\dots,2M-1\}$, $C$ a cell and $v\in V_C$. Every neighbour of $v$ in $H$ that is not in $V_C$ belongs to a group in $R(C)\cup O(C)$.
--
--   Differences from the source:
--   - generalization: the shift θ fixed as in Lemma 4.2 (PDF p. 16) → every shift θ ∈ {0, …, 2M − 1}; reason: the source's proof of this item never uses Lemma 4.2's bound; specializing θ to the fixed shift gives the source statement
--   - encoding: vertex set V(G) of size n → Fin n, with a rank representation ρ (fields l, r, injectivity, range 1..2n, l < r); reason: labelling the vertices 0..n−1 restricts no instance; the structure is exactly §4.1's representation
--   - encoding: cells as open intervals (ζ, ζ + D) of a binary tree → cells named by heap indices 1 ≤ C < 8M with explicit cellLo, cellLen; groups named by their least vertex; reason: a bijective naming of the same cells and groups; geometry recomputed from the index
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), Lemma 4.8, PDF p. 18 (printed p. 17)

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Hierarchy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntervalMaxCutEPTAS.Scheme

/-- Lemma 4.8: for `v ∈ V_C`, every neighbour of `v` in `H` outside `V_C` belongs to a group in
`R(C) ∪ O(C)`. -/
theorem lemma_4_8 {n : ℕ} (P : Setup n) (hb : 4 ≤ P.b) (hθ : P.θ < 2 * bigM n)
    (C : ℕ) (hC : IsCell n C) (v : Fin n) (hv : v ∈ VC P C) (u : Fin n) (hvu : (H P).Adj v u)
    (hu : u ∉ VC P C) :
    rep P u ∈ recent P C ∪ old P C := by sorry

end IntervalMaxCutEPTAS.Scheme
