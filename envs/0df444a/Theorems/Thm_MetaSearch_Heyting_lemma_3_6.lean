-- Prove2me | Theorems.Thm_MetaSearch_Heyting_lemma_3_6
-- name    : MetaSearch.Heyting.lemma_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:23:29.331107+00:00
-- url     : https://prove2.me/theorems/f4a88285-2917-4f54-ba26-f25951a7d224
-- title:
--   Lemma 3.6 — graded deduction: R ∧ T ≤ S implies T ≤ (R →_k S) for some k
-- statement:
--   Let $R,S,T$ be search problems with $R\wedge T\le S$. Then there is $k\in\mathbb N$ with
--   $$T\;\le\;(R\to_k S).$$
--
--   Differences from the source:
--   - encoding: Turing machines, polynomial time, and the encodings ⟨M⟩, ⟨x, y⟩ (no model fixed) → one concrete deterministic multi-tape Turing machine model (`Machine`, `Machine.evalWithin`, output on tape 0) with binary codes `Machine.encode`/`decode` and the pairing `pair x y` (bits of x doubled, then 01, then y); the bit b of ⟨x, b⟩ is the one-bit string [b]; reason: the paper fixes no model and its arguments only use that machines can be simulated, composed and padded with polynomial overhead, which holds in this model
-- source:
--   Ben-David, Ebtehaj, The Metacomplexity Structure of Search Problems, STOC 2027 submission (manuscript sha256 c3b015ea…), pp. 24-25, Lemma 3.6

import Mathlib
import Definitions.Def_MetaSearch_Heyting_Machine
import Definitions.Def_MetaSearch_Heyting_SearchProblem
import Definitions.Def_MetaSearch_Heyting_JoinMeet
import Definitions.Def_MetaSearch_Heyting_Refutation
import Definitions.Def_MetaSearch_Heyting_Ideal

namespace MetaSearch.Heyting

theorem lemma_3_6 (R S T : SearchProblem) (h : Reduces (meet R T) S) :
    ∃ k : ℕ, Reduces T (arrow k R S) := by sorry

end MetaSearch.Heyting
