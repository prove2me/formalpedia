-- Prove2me | Theorems.Thm_GagieRIndex_MacroScheme_lf_single_cycle
-- name    : GagieRIndex.MacroScheme.lf_single_cycle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:27:05.452016+00:00
-- url     : https://prove2.me/theorems/fe5460cf-7d71-4e68-b266-86d8c3376ee4
-- title:
--   §2.3, p. 8 — LF is a permutation formed by a single cycle
-- statement:
--   Let $T[1..n]$ be a text over $[1..\sigma]$ terminated by the unique smallest symbol $\$$, let $SA$ be its suffix array, and let $LF(p)=C[BWT[p]]+\operatorname{rank}[p]$ be the last-to-first mapping. Then $LF$ is a permutation of $[1..n]$ formed by a single cycle:
--
--   1. $LF$ maps $[1..n]$ into $[1..n]$;
--   2. $LF$ is injective on $[1..n]$;
--   3. every $p\in[1..n]$ is reached from position $1$, $p=LF^m(1)$ for some $0\le m<n$.
--
--   $$\{LF^m(1) : 0\le m<n\}=[1..n].$$
--
--   This is what lets the paper invert the BWT and, in Lemma 17, guarantees that every chain of copies in the DLCP macro scheme eventually reaches an explicit symbol.
--
--   **Formalization Note** "Single cycle" is stated as the orbit of position 1 covering $[1..n]$ within fewer than $n$ steps, together with injectivity on $[1..n]$.
-- source:
--   Gagie, Navarro, Prezza, Fully-Functional Suffix Trees and Optimal Text Searching in BWT-runs Bounded Space, arXiv:1809.02792v2, p. 8, §2.3, last sentence

import Mathlib
import Definitions.Def_GagieRIndex_MacroScheme_Arrays

namespace GagieRIndex.MacroScheme

theorem lf_single_cycle (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : GagieRIndex.Locate.IsText n σ T) (hSA : GagieRIndex.Locate.IsSuffixArray n T SA) :
    (∀ p, 1 ≤ p → p ≤ n → 1 ≤ GagieRIndex.Locate.LF n T SA p ∧ GagieRIndex.Locate.LF n T SA p ≤ n) ∧
    Set.InjOn (GagieRIndex.Locate.LF n T SA) (Set.Icc 1 n) ∧
    ∀ p, 1 ≤ p → p ≤ n → ∃ m < n, (GagieRIndex.Locate.LF n T SA)^[m] 1 = p := by sorry

end GagieRIndex.MacroScheme
