-- Prove2me | Theorems.Thm_GagieRIndex_MacroScheme_lemma_16
-- name    : GagieRIndex.MacroScheme.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:27:01.682242+00:00
-- url     : https://prove2.me/theorems/7b771be9-1848-4334-87e1-675465906add
-- title:
--   Lemma 16, p. 28 — inside a BWT run, LF is consecutive and preserves DLCP
-- statement:
--   Let $T[1..n]$ be a text terminated by the unique smallest symbol $\$$, with suffix array $SA$, Burrows–Wheeler transform $BWT$, last-to-first mapping $LF$ and differential LCP array $DLCP$. Let $3\le p\le n$ with $BWT[p-2]=BWT[p-1]=BWT[p]$, i.e. $[p-2,p]$ lies within a BWT run. Then
--   $$LF(p-1)=LF(p)-1\qquad\text{and}\qquad DLCP[LF(p)]=DLCP[p].$$
--
--   Three equal BWT symbols are needed because $DLCP[p]$ involves the three suffixes in cells $p-2$, $p-1$, $p$. The lemma is what makes the copies of the DLCP macro scheme of Lemma 17 correct.
-- source:
--   Gagie, Navarro, Prezza, Fully-Functional Suffix Trees and Optimal Text Searching in BWT-runs Bounded Space, arXiv:1809.02792v2, p. 28, Lemma 16

import Mathlib
import Definitions.Def_GagieRIndex_MacroScheme_Arrays

namespace GagieRIndex.MacroScheme

theorem lemma_16 (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : GagieRIndex.Locate.IsText n σ T) (hSA : GagieRIndex.Locate.IsSuffixArray n T SA)
    (p : ℕ) (hp3 : 3 ≤ p) (hpn : p ≤ n)
    (hrun1 : GagieRIndex.Locate.bwt n T SA (p - 2) = GagieRIndex.Locate.bwt n T SA (p - 1))
    (hrun2 : GagieRIndex.Locate.bwt n T SA (p - 1) = GagieRIndex.Locate.bwt n T SA p) :
    GagieRIndex.Locate.LF n T SA (p - 1) = GagieRIndex.Locate.LF n T SA p - 1 ∧
      DLCP n T SA (GagieRIndex.Locate.LF n T SA p) = DLCP n T SA p := by sorry

end GagieRIndex.MacroScheme
