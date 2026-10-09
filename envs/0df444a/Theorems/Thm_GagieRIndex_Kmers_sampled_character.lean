-- Prove2me | Theorems.Thm_GagieRIndex_Kmers_sampled_character
-- name    : GagieRIndex.Kmers.sampled_character
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:23:59.638212+00:00
-- url     : https://prove2.me/theorems/a1d8af5f-1d36-4035-b79e-3c42c10fcf8d
-- title:
--   Proof of Lemma 8, p. 17 — every text character has a sampled occurrence
-- statement:
--   Let $T[1..n]$ be a terminated text with a suffix array and BWT run-boundary samples. Every text character appears at a sampled text position:
--   $$\forall i\in[1..n],\quad\exists i'\in\operatorname{Sampled}(T),\quad T[i']=T[i].$$
--
--   This is the single-character base case of the primary-occurrence statement in Lemma 8.
--
--   **Formalization Note** The index $i$ is required to lie in $[1..n]$; the sampled set consists of text positions, not suffix-array cells.
-- source:
--   Gagie, Navarro, Prezza, Fully-Functional Suffix Trees and Optimal Text Searching in BWT-runs Bounded Space, arXiv:1809.02792v2, p. 17, proof of Lemma 8, second sentence

import Mathlib
import Definitions.Def_GagieRIndex_Locate_Core

namespace GagieRIndex.Kmers

theorem sampled_character (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : GagieRIndex.Locate.IsText n σ T) (hSA : GagieRIndex.Locate.IsSuffixArray n T SA)
    (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    ∃ i' ∈ GagieRIndex.Locate.sampled n T SA, T i' = T i := by sorry

end GagieRIndex.Kmers
