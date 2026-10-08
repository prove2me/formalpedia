-- Prove2me | Theorems.Thm_MatousekLP_Codes_even_pairs_ge_odd_pairs
-- name    : MatousekLP.Codes.even_pairs_ge_odd_pairs
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T13:02:38.895318+00:00
-- url     : https://prove2.me/theorems/f8f628db-bd0e-44e1-a923-2e65f50f96d8
-- title:
--   Lemma 8.4.5 — even restricted distances outnumber odd ones
-- statement:
--   Let $I \subseteq \{1,\dots,n\}$ be a set of indices and $C \subseteq \{0,1\}^n$ an arbitrary set of words. Write $d_H^I(\mathbf w,\mathbf w')$ for the number of indices $i \in I$ with $w_i \ne w'_i$. Then
--   $$
--   \bigl|\{(\mathbf w,\mathbf w') \in C^2 : d_H^I(\mathbf w,\mathbf w') \text{ odd}\}\bigr| \;\le\; \bigl|\{(\mathbf w,\mathbf w') \in C^2 : d_H^I(\mathbf w,\mathbf w') \text{ even}\}\bigr| .
--   $$
--   Pairs are ordered, and pairs $(\mathbf w,\mathbf w)$ are included.
--
--   This parity statement is the combinatorial core of Delsarte's inequalities: summed over suitable index sets it yields the Krawtchouk constraints of the linear program.
--
--   **Formalization Note** The index set $I$ is a `Finset (Fin n)` (positions shifted to $0,\dots,n-1$).
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 161, Lemma 8.4.5

import Mathlib
import Definitions.Def_MatousekLP_Codes_Basic

open Finset

namespace MatousekLP.Codes

/-- Lemma 8.4.5, p. 161: for every set of indices `I` and every `C ⊆ {0,1}^n`, the number of
ordered pairs `(w, w') ∈ C²` with `d_H^I(w, w')` even is at least the number of such pairs with
`d_H^I(w, w')` odd. -/
theorem even_pairs_ge_odd_pairs {n : ℕ} (I : Finset (Fin n)) (C : Finset (Word n)) :
    #{p ∈ C ×ˢ C | Odd (restrictedDist I p.1 p.2)} ≤
      #{p ∈ C ×ˢ C | Even (restrictedDist I p.1 p.2)} := by sorry

end MatousekLP.Codes
