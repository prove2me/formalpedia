-- Prove2me | Theorems.Thm_GagieRIndex_Locate_lemma_12
-- name    : GagieRIndex.Locate.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:22:47.233107+00:00
-- url     : https://prove2.me/theorems/57f00b25-b91b-4a48-8e0a-8c6b2272a9d9
-- title:
--   Lemma 12, p. 20 — inside a BWT run, LF is consecutive and preserves DSA
-- statement:
--   Let $T[1..n]$ be a text terminated by the unique smallest symbol $\$$, with suffix array $SA$, Burrows–Wheeler transform $BWT$, LF mapping $LF$ and differential suffix array $DSA$. Let $2\le p\le n$ and suppose $[p-1,p]$ lies within a BWT run, i.e. $BWT[p-1]=BWT[p]$. Then
--   $$LF(p-1)=LF(p)-1\qquad\text{and}\qquad DSA[LF(p)]=DSA[p].$$
--
--   Thus LF maps a run of the BWT onto a block of consecutive cells and copies the corresponding stretch of $DSA$. This is what makes the runs of the BWT induce repeated substrings in $DSA$.
--
--   **Formalization Note** "Within a BWT run" is encoded as $BWT[p-1]=BWT[p]$ with both positions in $[1..n]$.
-- source:
--   Gagie, Navarro, Prezza, Fully-Functional Suffix Trees and Optimal Text Searching in BWT-runs Bounded Space, arXiv:1809.02792v2, p. 20, Lemma 12

import Mathlib
import Definitions.Def_GagieRIndex_Locate_Arrays

namespace GagieRIndex.Locate

theorem lemma_12 (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : IsText n σ T) (hSA : IsSuffixArray n T SA)
    (p : ℕ) (hp2 : 2 ≤ p) (hpn : p ≤ n)
    (hrun : bwt n T SA (p - 1) = bwt n T SA p) :
    LF n T SA (p - 1) = LF n T SA p - 1 ∧
      DSA SA (LF n T SA p) = DSA SA p := by sorry

end GagieRIndex.Locate
