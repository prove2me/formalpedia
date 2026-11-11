-- Prove2me | Theorems.Thm_MetaSearch_Heyting_lemma_2_11
-- name    : MetaSearch.Heyting.lemma_2_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:23:38.567195+00:00
-- url     : https://prove2.me/theorems/dd458d36-c83f-431d-95d1-0b73f4170238
-- title:
--   Lemma 2.11 — Verifiable is closed under the meet ∧
-- statement:
--   For search problems $S_0,S_1$ (Definition 2.10 gives $S_0\wedge S_1$):
--   $$S_0,S_1\in\mathsf{Verifiable}\;\Longrightarrow\;S_0\wedge S_1\in\mathsf{Verifiable}.$$
--
--   Differences from the source:
--   - encoding: Turing machines, polynomial time, and the encodings ⟨M⟩, ⟨x, y⟩ (no model fixed) → one concrete deterministic multi-tape Turing machine model (`Machine`, `Machine.evalWithin`, output on tape 0) with binary codes `Machine.encode`/`decode` and the pairing `pair x y` (bits of x doubled, then 01, then y); the bit b of ⟨x, b⟩ is the one-bit string [b]; reason: the paper fixes no model and its arguments only use that machines can be simulated, composed and padded with polynomial overhead, which holds in this model
-- source:
--   Ben-David, Ebtehaj, The Metacomplexity Structure of Search Problems, STOC 2027 submission (manuscript sha256 c3b015ea…), p. 19, Lemma 2.11

import Mathlib
import Definitions.Def_MetaSearch_Heyting_Machine
import Definitions.Def_MetaSearch_Heyting_SearchProblem
import Definitions.Def_MetaSearch_Heyting_JoinMeet
import Definitions.Def_MetaSearch_Heyting_Refutation
import Definitions.Def_MetaSearch_Heyting_Ideal

namespace MetaSearch.Heyting

theorem lemma_2_11 (S₀ S₁ : SearchProblem) (h₀ : S₀ ∈ Verifiable)
    (h₁ : S₁ ∈ Verifiable) : meet S₀ S₁ ∈ Verifiable := by sorry

end MetaSearch.Heyting
