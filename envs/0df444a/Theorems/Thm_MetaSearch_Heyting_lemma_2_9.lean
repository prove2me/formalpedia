-- Prove2me | Theorems.Thm_MetaSearch_Heyting_lemma_2_9
-- name    : MetaSearch.Heyting.lemma_2_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:23:39.712197+00:00
-- url     : https://prove2.me/theorems/3198c92a-0dcc-4df3-a8c8-2ff5e451a94a
-- title:
--   Lemma 2.9 — S₀ ∨ S₁ is a join (least upper bound) in (Search, ≤)
-- statement:
--   For all search problems $S_0,S_1$: $S_0\le S_0\vee S_1$ and $S_1\le S_0\vee S_1$, and for every search problem $T$,
--   $$S_0\le T\ \text{and}\ S_1\le T\;\Longrightarrow\;S_0\vee S_1\le T.$$
--   So $S_0\vee S_1$ is a join of $S_0$ and $S_1$ in the preorder $\le$ on all search problems.
--
--   Differences from the source:
--   - reading: 'In other words, S0 ∨ S1 is a join of S0 and S1 in the preorder ≤ on Search' → the upper-bound property S_b ≤ S0 ∨ S1 (the paper's Lemma 2.8) is stated as a conjunct next to the least-upper-bound implication; reason: a join is an upper bound that is least; the sentence asserts both, and Lemma 2.8 supplies the first half
--   - encoding: Turing machines, polynomial time, and the encodings ⟨M⟩, ⟨x, y⟩ (no model fixed) → one concrete deterministic multi-tape Turing machine model (`Machine`, `Machine.evalWithin`, output on tape 0) with binary codes `Machine.encode`/`decode` and the pairing `pair x y` (bits of x doubled, then 01, then y); the bit b of ⟨x, b⟩ is the one-bit string [b]; reason: the paper fixes no model and its arguments only use that machines can be simulated, composed and padded with polynomial overhead, which holds in this model
-- source:
--   Ben-David, Ebtehaj, The Metacomplexity Structure of Search Problems, STOC 2027 submission (manuscript sha256 c3b015ea…), p. 18, Lemma 2.9

import Mathlib
import Definitions.Def_MetaSearch_Heyting_Machine
import Definitions.Def_MetaSearch_Heyting_SearchProblem
import Definitions.Def_MetaSearch_Heyting_JoinMeet
import Definitions.Def_MetaSearch_Heyting_Refutation
import Definitions.Def_MetaSearch_Heyting_Ideal

namespace MetaSearch.Heyting

theorem lemma_2_9 (S₀ S₁ : SearchProblem) :
    (Reduces S₀ (join S₀ S₁) ∧ Reduces S₁ (join S₀ S₁)) ∧
    ∀ T : SearchProblem, Reduces S₀ T → Reduces S₁ T → Reduces (join S₀ S₁) T := by sorry

end MetaSearch.Heyting
