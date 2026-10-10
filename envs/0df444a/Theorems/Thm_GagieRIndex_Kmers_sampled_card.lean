-- Prove2me | Theorems.Thm_GagieRIndex_Kmers_sampled_card
-- name    : GagieRIndex.Kmers.sampled_card
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T21:24:01.887461+00:00
-- url     : https://prove2.me/theorems/db871a41-6875-4c22-b2d5-335ccb63a47f
-- title:
--   Proof of Lemma 9, p. 17 — at most 2r sampled positions
-- statement:
--   Let $r$ be the number of runs in the BWT of $T$, and let $\operatorname{Sampled}(T)$ be the set of text positions corresponding to the first or last character of a run. Then
--   $$|\operatorname{Sampled}(T)|\le 2r.$$
--
--   This count is used with Lemma 8 to bound the number of distinct length-$s$ substrings.
--
--   **Formalization Note** The set is an image of run-boundary BWT cells under the wrapped predecessor-position map. Repeated text positions are counted once.
-- source:
--   Gagie, Navarro, Prezza, Fully-Functional Suffix Trees and Optimal Text Searching in BWT-runs Bounded Space, arXiv:1809.02792v2, p. 17, proof of Lemma 9, second sentence

import Mathlib
import Definitions.Def_GagieRIndex_Locate_Core

namespace GagieRIndex.Kmers

theorem sampled_card (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : GagieRIndex.Locate.IsText n σ T) (hSA : GagieRIndex.Locate.IsSuffixArray n T SA) :
    (GagieRIndex.Locate.sampled n T SA).card ≤ 2 * GagieRIndex.Locate.runs n T SA := by sorry

end GagieRIndex.Kmers
