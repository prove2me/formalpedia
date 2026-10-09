-- Prove2me | Theorems.Thm_GagieRIndex_MacroScheme_lemma_17
-- name    : GagieRIndex.MacroScheme.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:27:23.659796+00:00
-- url     : https://prove2.me/theorems/5f0db6f1-d2cb-4a60-b24c-edeb521a0ec6
-- title:
--   Lemma 17, p. 28 — the run-induced partition of DLCP is a bidirectional macro scheme
-- statement:
--   Let $T[1..n]$ be a text terminated by the unique smallest symbol $\$$, with suffix array $SA$, and let $p_1<\dots<p_r$ be the positions that start runs in $BWT$, with the conventions $p_0=-2$ and $p_{r+1}=n+1$. Consider the partition of $DLCP[1..n]$ formed by
--
--   1. the explicit symbols $DLCP[p_i+k]$ for $1\le i\le r$ and $k\in\{0,1,2\}$, and
--   2. the nonempty regions $DLCP[p_i+3..p_{i+1}-1]$, $0\le i\le r$, each pointing to $DLCP[LF(p_i+3)..LF(p_{i+1}-1)]$.
--
--   This partition is a bidirectional macro scheme of $DLCP$.
--
--   The lemma is the explicit content behind the bound $4r+1$ on the size of a macro scheme for $DLCP$, which feeds the $O(r\log(n/r))$ grammar of Lemma 19.
--
--   **Formalization Note** The partition is characterised rather than constructed: there is a macro scheme of $DLCP$ whose explicit blocks are exactly the singleton blocks at explicit cells (cells $x\le n$ with $x\in\{p_i,p_i+1,p_i+2\}$; cells beyond $n$ do not exist, and overlapping cells of short runs are counted once), and whose pointer blocks are exactly the maximal stretches of non-explicit cells (preceded by an explicit cell, followed by an explicit cell or the end), each pointing to the stretch starting at $LF$ of its first cell. Every cell in a pointer block maps under $LF$ to the corresponding cell of that source stretch, including its endpoint. The convention $p_0=-2$ only makes the region before $p_1=1$ empty and needs no encoding.
-- source:
--   Gagie, Navarro, Prezza, Fully-Functional Suffix Trees and Optimal Text Searching in BWT-runs Bounded Space, arXiv:1809.02792v2, p. 28, Lemma 17 (with Definition 6)

import Mathlib
import Definitions.Def_GagieRIndex_MacroScheme_Arrays
import Definitions.Def_GagieRIndex_MacroScheme_BMS

namespace GagieRIndex.MacroScheme

theorem lemma_17 (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : GagieRIndex.Locate.IsText n σ T) (hSA : GagieRIndex.Locate.IsSuffixArray n T SA) :
    ∃ B : List Block, IsBMS n (DLCP n T SA) B ∧
      (∀ k (hk : k < B.length), (B[k]).src = none ↔ IsExplicit17 n T SA (blockStart B k)) ∧
      (∀ k (hk : k < B.length), ∀ j, (B[k]).src = some j →
          j = GagieRIndex.Locate.LF n T SA (blockStart B k) ∧
          (∀ t < (B[k]).len,
            GagieRIndex.Locate.LF n T SA (blockStart B k + t) = j + t) ∧
          (∀ t < (B[k]).len, ¬ IsExplicit17 n T SA (blockStart B k + t)) ∧
          IsExplicit17 n T SA (blockStart B k - 1) ∧
          (blockStart B k + (B[k]).len = n + 1 ∨
            IsExplicit17 n T SA (blockStart B k + (B[k]).len))) := by sorry

end GagieRIndex.MacroScheme
