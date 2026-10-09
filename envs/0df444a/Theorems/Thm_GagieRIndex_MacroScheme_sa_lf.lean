-- Prove2me | Theorems.Thm_GagieRIndex_MacroScheme_sa_lf
-- name    : GagieRIndex.MacroScheme.sa_lf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:26:38.657984+00:00
-- url     : https://prove2.me/theorems/8371555f-780f-472b-b881-e8a095f4ba43
-- title:
--   §2.4, p. 9 — SA[LF(p)] = SA[p] − 1
-- statement:
--   Let $T[1..n]$ be a text terminated by the unique smallest symbol $\$$, let $SA$ be its suffix array and $LF$ its last-to-first mapping. For every $p\in[1..n]$, $LF(p)\in[1..n]$, and if $SA[p]>1$ then
--   $$SA[LF(p)]=SA[p]-1.$$
--
--   $LF$ walks the text backwards: it sends the cell of a suffix to the cell of the suffix that starts one position earlier. This is the basic step of locating and extracting with an FM-index.
--
--   **Formalization Note** The page states the identity for every $p$; it holds literally only when $SA[p]>1$. For $SA[p]=1$ the BWT symbol is $T[n]=\$$ and the identity holds cyclically ($SA[LF(p)]=n$), so the guard $SA[p]>1$ is added.
-- source:
--   Gagie, Navarro, Prezza, Fully-Functional Suffix Trees and Optimal Text Searching in BWT-runs Bounded Space, arXiv:1809.02792v2, p. 9, §2.4, displayed equation

import Mathlib
import Definitions.Def_GagieRIndex_MacroScheme_Arrays

namespace GagieRIndex.MacroScheme

theorem sa_lf (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : GagieRIndex.Locate.IsText n σ T) (hSA : GagieRIndex.Locate.IsSuffixArray n T SA)
    (p : ℕ) (hp1 : 1 ≤ p) (hpn : p ≤ n) :
    1 ≤ GagieRIndex.Locate.LF n T SA p ∧ GagieRIndex.Locate.LF n T SA p ≤ n ∧
      (1 < SA p → SA (GagieRIndex.Locate.LF n T SA p) = SA p - 1) := by sorry

end GagieRIndex.MacroScheme
