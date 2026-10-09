-- Prove2me | Theorems.Thm_GagieRIndex_MacroScheme_bms_size
-- name    : GagieRIndex.MacroScheme.bms_size
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:44.046374+00:00
-- url     : https://prove2.me/theorems/3acfb128-11f2-4c4d-9d4d-52aa0669afd8
-- title:
--   §6.2, p. 28 — DLCP has a bidirectional macro scheme of size at most 4r + 1
-- statement:
--   Let $T[1..n]$ be a text over $[1..\sigma]$ terminated by the unique smallest symbol $\$$, let $SA$ be its suffix array, and let $r$ be the number of runs of its Burrows–Wheeler transform. Then the differential LCP array $DLCP[1..n]$ (with $DLCP[1]=LCP[1]$ and $DLCP[i]=LCP[i]-LCP[i-1]$ for $i>1$) has a bidirectional macro scheme of size $b$ with
--   $$b\le 4r+1.$$
--
--   Every sequence of length $n$ has a macro scheme of size $n$; the content is that the size is bounded by the number of BWT runs, which is small for repetitive texts. Combined with the conversion of a macro scheme into a run-length grammar (Lemma 18, cited), this yields the $O(r\log(n/r))$-size grammar for $DLCP$ behind the paper's compressed suffix tree.
--
--   **Formalization Note** "Macro scheme" means a correct bidirectional macro scheme in the sense of Definition 6, including the condition that every chain of copies reaches an explicit symbol; the bound $4r+1$ is the paper's.
-- source:
--   Gagie, Navarro, Prezza, Fully-Functional Suffix Trees and Optimal Text Searching in BWT-runs Bounded Space, arXiv:1809.02792v2, p. 28, §6.2 (sentence after Lemma 16; proved by Lemma 17)

import Mathlib
import Definitions.Def_GagieRIndex_MacroScheme_Arrays
import Definitions.Def_GagieRIndex_MacroScheme_BMS

namespace GagieRIndex.MacroScheme

theorem bms_size (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : GagieRIndex.Locate.IsText n σ T) (hSA : GagieRIndex.Locate.IsSuffixArray n T SA) :
    ∃ B : List Block, IsBMS n (DLCP n T SA) B ∧ B.length ≤ 4 * GagieRIndex.Locate.runs n T SA + 1 := by sorry

end GagieRIndex.MacroScheme
