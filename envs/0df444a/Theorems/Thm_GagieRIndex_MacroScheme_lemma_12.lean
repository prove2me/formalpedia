-- Prove2me | Theorems.Thm_GagieRIndex_MacroScheme_lemma_12
-- name    : GagieRIndex.MacroScheme.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:53.339989+00:00
-- url     : https://prove2.me/theorems/7bb9790e-6b3d-4995-aaa4-af5620e983cc
-- title:
--   Lemma 12, p. 20 — inside a BWT run, LF is consecutive and preserves DSA
-- statement:
--   Let $T[1..n]$ be a text terminated by the unique smallest symbol $\$$, with suffix array $SA$, Burrows–Wheeler transform $BWT$, last-to-first mapping $LF$ and differential suffix array $DSA$. Let $2\le p\le n$ with $BWT[p-1]=BWT[p]$, i.e. $[p-1,p]$ lies within a BWT run. Then
--   $$LF(p-1)=LF(p)-1\qquad\text{and}\qquad DSA[LF(p)]=DSA[p].$$
--
--   Runs of the BWT are therefore copied, under $LF$, into repeated stretches of $DSA$; this is the source of the compressibility of $DSA$ in §5.2.
-- source:
--   Gagie, Navarro, Prezza, Fully-Functional Suffix Trees and Optimal Text Searching in BWT-runs Bounded Space, arXiv:1809.02792v2, p. 20, Lemma 12

import Mathlib
import Definitions.Def_GagieRIndex_MacroScheme_Arrays

namespace GagieRIndex.MacroScheme

theorem lemma_12 (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : GagieRIndex.Locate.IsText n σ T) (hSA : GagieRIndex.Locate.IsSuffixArray n T SA)
    (p : ℕ) (hp2 : 2 ≤ p) (hpn : p ≤ n)
    (hrun : GagieRIndex.Locate.bwt n T SA (p - 1) = GagieRIndex.Locate.bwt n T SA p) :
    GagieRIndex.Locate.LF n T SA (p - 1) = GagieRIndex.Locate.LF n T SA p - 1 ∧
      GagieRIndex.Locate.DSA SA (GagieRIndex.Locate.LF n T SA p) = GagieRIndex.Locate.DSA SA p := by sorry

end GagieRIndex.MacroScheme
