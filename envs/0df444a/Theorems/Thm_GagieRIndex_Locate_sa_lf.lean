-- Prove2me | Theorems.Thm_GagieRIndex_Locate_sa_lf
-- name    : GagieRIndex.Locate.sa_lf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:20:08.153375+00:00
-- url     : https://prove2.me/theorems/d57cfab0-a595-446b-b155-1707627bc13b
-- title:
--   §2.4, p. 9 — LF traverses the text backwards: SA[LF(p)] = SA[p] − 1
-- statement:
--   Let $T[1..n]$ be a text terminated by the unique smallest symbol $\$$, with suffix array $SA$, Burrows–Wheeler transform $BWT$ and LF mapping $LF(p)=C[BWT[p]]+\operatorname{rank}[p]$. For every position $1\le p\le n$, $LF(p)$ is again a position in $[1..n]$, and if $SA[p]>1$ then
--   $$SA[LF(p)]=SA[p]-1.$$
--
--   In words, the counting formula for LF moves from the BWT character that precedes the suffix $T[SA[p]..]$ to the suffix-array cell of the suffix starting with that character: LF walks the text backwards one position at a time. This is the basic step of every backward traversal in the paper.
--
--   **Formalization Note** The page writes the identity without the guard $SA[p]>1$. When $SA[p]=1$ (so $BWT[p]=\$$), $LF(p)=1$ and $SA[1]=n$: the identity then holds only cyclically, reading $0$ as $n$, and natural-number subtraction would make the literal display false. The range conclusion $1\le LF(p)\le n$ is the page's "its position $F[q]$".
-- source:
--   Gagie, Navarro, Prezza, Fully-Functional Suffix Trees and Optimal Text Searching in BWT-runs Bounded Space, arXiv:1809.02792v2, p. 9, §2.4, display SA[LF(p)] = SA[p] − 1

import Mathlib
import Definitions.Def_GagieRIndex_Locate_Core

namespace GagieRIndex.Locate

theorem sa_lf (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : IsText n σ T) (hSA : IsSuffixArray n T SA)
    (p : ℕ) (hp1 : 1 ≤ p) (hpn : p ≤ n) :
    1 ≤ LF n T SA p ∧ LF n T SA p ≤ n ∧
      (1 < SA p → SA (LF n T SA p) = SA p - 1) := by sorry

end GagieRIndex.Locate
