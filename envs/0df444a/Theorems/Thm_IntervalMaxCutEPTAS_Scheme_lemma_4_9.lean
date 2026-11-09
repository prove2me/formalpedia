-- Prove2me | Theorems.Thm_IntervalMaxCutEPTAS_Scheme_lemma_4_9
-- name    : IntervalMaxCutEPTAS.Scheme.lemma_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:18:13.682195+00:00
-- url     : https://prove2.me/theorems/fe465194-b2e4-46bc-9b6a-641e2d53878b
-- title:
--   Lemma 4.9 — recent and old groups along the tree
-- statement:
--   Let $b\ge4$, $\sigma=2^{-b}$, $\tau=2b$, $\theta\in\{0,\dots,2M-1\}$, $C$ a cell and $C'$ a child of $C$.
--
--   1. $R(C')\subseteq R(C)\cup A(C)$.
--   2. $O(C)\subseteq O(C')$, and $O(C')\setminus O(C)\subseteq R(C)$.
--   3. A group in $R(C)\cup A(C)$ that belongs neither to $R(C')$ nor to $O(C')$ has no neighbour in $V_{C'}$.
--   4. $|A(C)|+|R(C)|\le\tau(b+1)(2/\sigma+1)^2$ (for every cell $C$).
--
--   Differences from the source:
--   - generalization: the shift θ fixed as in Lemma 4.2 (PDF p. 16) → every shift θ ∈ {0, …, 2M − 1}; reason: the source's proof of this item never uses Lemma 4.2's bound; specializing θ to the fixed shift gives the source statement
--   - encoding: vertex set V(G) of size n → Fin n, with a rank representation ρ (fields l, r, injectivity, range 1..2n, l < r); reason: labelling the vertices 0..n−1 restricts no instance; the structure is exactly §4.1's representation
--   - encoding: cells as open intervals (ζ, ζ + D) of a binary tree → cells named by heap indices 1 ≤ C < 8M with explicit cellLo, cellLen; groups named by their least vertex; reason: a bijective naming of the same cells and groups; geometry recomputed from the index
--   - encoding: τ(b + 1)(2/σ + 1)² → 2b(b + 1)(2^{b+1} + 1)²; reason: exact value
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), Lemma 4.9, PDF p. 18 (printed p. 17)

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Hierarchy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntervalMaxCutEPTAS.Scheme

/-- Lemma 4.9: for a cell `C` and a child `C'` of `C`, (a) `R(C') ⊆ R(C) ∪ A(C)`;
(b) `O(C) ⊆ O(C')` and `O(C') \ O(C) ⊆ R(C)`; (c) a group in `R(C) ∪ A(C)` in neither `R(C')`
nor `O(C')` has no neighbour in `V_{C'}`; and (d) `|A(C)| + |R(C)| ≤ τ(b + 1)(2/σ + 1)²`. -/
theorem lemma_4_9 {n : ℕ} (P : Setup n) (hb : 4 ≤ P.b) (hθ : P.θ < 2 * bigM n)
    (C : ℕ) (hC : IsCell n C) :
    (∀ C', ¬ IsLeaf n C → (C' = 2 * C ∨ C' = 2 * C + 1) →
      recent P C' ⊆ recent P C ∪ own P C ∧
      (old P C ⊆ old P C' ∧ old P C' \ old P C ⊆ recent P C) ∧
      (∀ g ∈ recent P C ∪ own P C, g ∉ recent P C' → g ∉ old P C' →
        ∀ u ∈ groupOf P g, ∀ v ∈ VC P C', ¬ (H P).Adj u v)) ∧
    (own P C).card + (recent P C).card ≤ 2 * P.b * (P.b + 1) * (2 ^ (P.b + 1) + 1) ^ 2 := by sorry

end IntervalMaxCutEPTAS.Scheme
