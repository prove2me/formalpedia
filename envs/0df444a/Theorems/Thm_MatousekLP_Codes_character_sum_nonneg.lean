-- Prove2me | Theorems.Thm_MatousekLP_Codes_character_sum_nonneg
-- name    : MatousekLP.Codes.character_sum_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T13:02:48.532741+00:00
-- url     : https://prove2.me/theorems/713dc28f-4728-4d5d-957f-a3029855631e
-- title:
--   Corollary 8.4.6 — $\sum_{(w,w')\in C^2}(-1)^{(w\oplus w')^T v} \ge 0$
-- statement:
--   For every set of words $C \subseteq \{0,1\}^n$ and every word $\mathbf v \in \{0,1\}^n$,
--   $$
--   \sum_{(\mathbf w,\mathbf w') \in C^2} (-1)^{(\mathbf w \oplus \mathbf w')^T \mathbf v} \;\ge\; 0,
--   $$
--   where $\mathbf w \oplus \mathbf w'$ is the sum modulo 2 and $\mathbf u^T\mathbf v$ is the scalar product of 0/1 vectors, i.e. the number of positions where both $\mathbf u$ and $\mathbf v$ have a one.
--
--   This is the sign form of Lemma 8.4.5 used in the proof of Proposition 8.4.4.
--
--   **Formalization Note** The sum is over the ordered pairs of `C ×ˢ C`, computed in $\mathbb Z$; $(\mathbf w\oplus\mathbf w')^T\mathbf v$ is a natural number.
-- source:
--   Matoušek & Gärtner, Understanding and Using Linear Programming, Springer 2007, p. 161, Corollary 8.4.6

import Mathlib
import Definitions.Def_MatousekLP_Codes_Basic

open Finset

namespace MatousekLP.Codes

/-- Corollary 8.4.6, p. 161: for every `C ⊆ {0,1}^n` and every `v ∈ {0,1}^n`,
`∑_{(w,w') ∈ C²} (-1)^{(w ⊕ w')ᵀ v} ≥ 0`. -/
theorem character_sum_nonneg {n : ℕ} (C : Finset (Word n)) (v : Word n) :
    0 ≤ ∑ p ∈ C ×ˢ C, (-1 : ℤ) ^ dot (xorWord p.1 p.2) v := by sorry

end MatousekLP.Codes
