-- Prove2me | Theorems.Thm_ModLatSVP_chain_refinement
-- name    : ModLatSVP.chain_refinement
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:11:56.482325+00:00
-- url     : https://prove2.me/theorems/86fc28d2-e262-4f0f-a8a8-1e2fbc265201
-- title:
--   Chain refinement — a bounded chain can be refined to one through maximal proper subfields
-- statement:
--   Let $K$ be a number field that has a subfield chain $K=K_0\supsetneq K_1\supsetneq\cdots\supsetneq K_h$ with $[K_j:K_{j+1}]\le s_0$ and $[K_h:\mathbb Q]\le d_0$. Then $K$ has a chain with the same bounds and the same last field $K_h$ in which every step is maximal: for each $j$, no subfield lies strictly between $K_{j+1}$ and $K_j$.
--
--   The refined steps divide the original indices, so they stay at most $s_0$. This shows that the search of Lemma 3.6(i), which only follows maximal (hence principal) subfields, is complete.
--
--   Differences from the source:
--   - generalization: K totally real or CM (standing hypothesis of Lemma 3.6) → any number field K; reason: the refinement only uses that K has finitely many subfields and the tower law; specializes to the source
--   - reading: Refine each step through maximal proper intermediate subfields. … each remains at most s₀ → there is a chain (IsChain with the same s₀, d₀) ending at the same field whose every step K_j ⊋ K_{j+1} is maximal; reason: the sentence asserts the existence of the refined chain with the bounds
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), proof of Lemma 3.6, p.22 (PDF p.22)

import Mathlib
import Definitions.Def_ModLatSVP_IsChain

namespace ModLatSVP

/-- **Chain refinement, proof of Lemma 3.6, p.22.** Kim, Lee, Son, *Exact SVP and CVP in Structured
Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027 submission (manuscript sha256
e7151fad…): "To see that this search is complete, suppose a chain satisfying the required bounds exists.
Refine each step through maximal proper intermediate subfields. The indices of the refined steps
multiply to the original index, so each remains at most s₀."

If `K` has a chain `K = K₀ ⊋ ⋯ ⊋ K_h` with `[K_j : K_{j+1}] ≤ s₀` and `[K_h : ℚ] ≤ d₀`, then it has such a
chain, ending at the same field `K_h`, in which every `K_{j+1}` is a maximal proper subfield of `K_j`: no
subfield lies strictly between them.

**Formalization Note.** Stated for every number field (the paper's `K` is totally real or CM; the
refinement does not use it). -/
theorem chain_refinement (K : Type*) [Field K] [NumberField K] (s₀ d₀ : ℕ) (h : ℕ)
    (F : ℕ → IntermediateField ℚ K) (hF : IsChain K s₀ d₀ F h) :
    ∃ (h' : ℕ) (F' : ℕ → IntermediateField ℚ K), IsChain K s₀ d₀ F' h' ∧ F' h' = F h ∧
      ∀ j < h', ∀ E : IntermediateField ℚ K, F' (j + 1) ≤ E → E ≤ F' j →
        E = F' (j + 1) ∨ E = F' j := by sorry

end ModLatSVP
