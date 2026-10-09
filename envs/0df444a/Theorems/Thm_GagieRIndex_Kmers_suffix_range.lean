-- Prove2me | Theorems.Thm_GagieRIndex_Kmers_suffix_range
-- name    : GagieRIndex.Kmers.suffix_range
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:24:05.497999+00:00
-- url     : https://prove2.me/theorems/248f46af-bac8-456f-b393-7cc3b360d778
-- title:
--   §2.1, p. 7 — suffixes beginning with a pattern occupy one suffix-array range
-- statement:
--   Let $T[1..n]$ be a terminated text, $SA[1..n]$ its suffix array, and $P$ any finite pattern. The suffixes beginning with $P$ occupy one contiguous suffix-array range:
--   $$\{p\in[1..n]:P\text{ is a prefix of }T[SA[p]..n]\}=[sp..ep]\cap[1..n]$$
--   for some endpoints $sp,ep$. If no suffix begins with $P$, the interval is empty.
--
--   This range is the basic form in which pattern occurrences are found by suffix-array search and used in the proof of Lemma 8.
--
--   **Formalization Note** The empty range is represented by endpoints with $sp>ep$. No restriction on the symbols of $P$ is needed.
-- source:
--   Gagie, Navarro, Prezza, Fully-Functional Suffix Trees and Optimal Text Searching in BWT-runs Bounded Space, arXiv:1809.02792v2, p. 7, §2.1, fourth paragraph

import Mathlib
import Definitions.Def_GagieRIndex_Locate_Core

namespace GagieRIndex.Kmers

theorem suffix_range (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : GagieRIndex.Locate.IsText n σ T) (hSA : GagieRIndex.Locate.IsSuffixArray n T SA) (P : List ℕ) :
    ∃ sp ep, ∀ p, 1 ≤ p → p ≤ n → (P <+: GagieRIndex.Locate.suffix n T (SA p) ↔ sp ≤ p ∧ p ≤ ep) := by sorry

end GagieRIndex.Kmers
