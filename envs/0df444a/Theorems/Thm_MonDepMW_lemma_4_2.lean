-- Prove2me | Theorems.Thm_MonDepMW_lemma_4_2
-- name    : MonDepMW.lemma_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:48:45.803636+00:00
-- url     : https://prove2.me/theorems/a7e0b11f-02ac-457a-a7f7-6f1acbda9909
-- title:
--   Lemma 4.2 — additivity of 1-types
-- statement:
--   Let $G$ be a graph and $\gamma\geqslant1$ be such that $|\mathcal T_1(G,A)|\leqslant\gamma|A|$ for every non-empty $A\subseteq V(G)$. Let $S_1,\dots,S_t,X\subseteq V(G)$, and for each $i\in[t]$ let $k_i$ be the number of 1-types over $S_i$ intersected by $X$. Then the number of 1-types over $S=\bigcup_{i\in[t]}S_i$ intersected by $X$ is at most
--   $$\gamma\sum_{i\in[t]}k_i.$$
--
--   The lemma assembles the per-step bounds in the proof of Theorem 4.3.
--
--   Differences from the source:
--   - reading: S1, …, St with [t] for t ∈ N → 1 ≤ t; reason: the paper’s N is positive; at t = 0 the sum is 0 while a non-empty X meets the one type over ∅
-- source:
--   Dreier, Mählmann, Pilipczuk, Toruńczyk, Monadically Dependent Graph Classes Have Almost Bounded Merge-Width, arXiv:2611.06804 (held version, sha256 6e4b0608…), Lemma 4.2, p.15

import Mathlib
import Definitions.Def_MonDepMW_oneType

set_option autoImplicit false

namespace MonDepMW

/-- **Lemma 4.2.** Dreier, Mählmann, Pilipczuk, Toruńczyk, *Monadically Dependent Graph Classes Have Almost Bounded Merge-Width*, arXiv:2611.06804 (held version, sha256 6e4b0608…), p.15: "Let G be a graph and γ ∈ N be such that |𝒯1(G, A)| ⩽ γ|A| for every non-empty A ⊆ V (G). Let
S1, . . . , St, X ⊆ V (G) be vertex subsets. Further, for every i ∈ [t], let ki be the number of 1-types over Si that are
intersected by X. Then the number of 1-types over S := ⋃_{i∈[t]} Si intersected by X is bounded by γ · Σ_{i∈[t]} ki."

**Formalization Note.** `t ∈ N` is positive; at `t = 0` the sum is `0` while a non-empty `X` meets the one type over `∅`.
`γ ∈ N` is `1 ≤ γ`. -/
theorem lemma_4_2 {n : ℕ} (G : SimpleGraph (Fin n)) (γ : ℕ) (hγ : 1 ≤ γ)
    (hG : ∀ A : Finset (Fin n), A.Nonempty → numParts (oneType G A) ≤ γ * A.card)
    (t : ℕ) (ht : 1 ≤ t) (S : Fin t → Finset (Fin n)) (X : Set (Fin n)) :
    partsHit (oneType G (Finset.univ.biUnion S)) X ≤
      γ * ∑ i, partsHit (oneType G (S i)) X := by sorry

end MonDepMW
