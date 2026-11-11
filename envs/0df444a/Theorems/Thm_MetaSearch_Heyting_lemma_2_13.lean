-- Prove2me | Theorems.Thm_MetaSearch_Heyting_lemma_2_13
-- name    : MetaSearch.Heyting.lemma_2_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:23:32.705754+00:00
-- url     : https://prove2.me/theorems/78bc9cc5-07a0-4b10-a0eb-361c63e04d1a
-- title:
--   Lemma 2.13 — S₀ ∧ S₁ is a meet (greatest lower bound) in (Search, ≤)
-- statement:
--   For all search problems $S_0,S_1$: $S_0\wedge S_1\le S_0$ and $S_0\wedge S_1\le S_1$, and for every search problem $R$,
--   $$R\le S_0\ \text{and}\ R\le S_1\;\Longrightarrow\;R\le S_0\wedge S_1.$$
--   So $S_0\wedge S_1$ is a meet of $S_0$ and $S_1$ in the preorder $\le$ on all search problems.
--
--   Differences from the source:
--   - reading: 'In other words, S0 ∧ S1 is a meet of S0 and S1 in the preorder ≤ on Search' → the lower-bound property S0 ∧ S1 ≤ S_b (the paper's Lemma 2.12) is stated as a conjunct next to the greatest-lower-bound implication; reason: a meet is a lower bound that is greatest; the sentence asserts both, and Lemma 2.12 supplies the first half
--   - encoding: Turing machines, polynomial time, and the encodings ⟨M⟩, ⟨x, y⟩ (no model fixed) → one concrete deterministic multi-tape Turing machine model (`Machine`, `Machine.evalWithin`, output on tape 0) with binary codes `Machine.encode`/`decode` and the pairing `pair x y` (bits of x doubled, then 01, then y); the bit b of ⟨x, b⟩ is the one-bit string [b]; reason: the paper fixes no model and its arguments only use that machines can be simulated, composed and padded with polynomial overhead, which holds in this model
-- source:
--   Ben-David, Ebtehaj, The Metacomplexity Structure of Search Problems, STOC 2027 submission (manuscript sha256 c3b015ea…), p. 19, Lemma 2.13

import Mathlib
import Definitions.Def_MetaSearch_Heyting_Machine
import Definitions.Def_MetaSearch_Heyting_SearchProblem
import Definitions.Def_MetaSearch_Heyting_JoinMeet
import Definitions.Def_MetaSearch_Heyting_Refutation
import Definitions.Def_MetaSearch_Heyting_Ideal

namespace MetaSearch.Heyting

theorem lemma_2_13 (S₀ S₁ : SearchProblem) :
    (Reduces (meet S₀ S₁) S₀ ∧ Reduces (meet S₀ S₁) S₁) ∧
    ∀ R : SearchProblem, Reduces R S₀ → Reduces R S₁ → Reduces R (meet S₀ S₁) := by sorry

end MetaSearch.Heyting
