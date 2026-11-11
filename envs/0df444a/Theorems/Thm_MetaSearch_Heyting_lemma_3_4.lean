-- Prove2me | Theorems.Thm_MetaSearch_Heyting_lemma_3_4
-- name    : MetaSearch.Heyting.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:23:47.921409+00:00
-- url     : https://prove2.me/theorems/29ac871c-5150-4850-b69a-1a27c4399f4a
-- title:
--   Lemma 3.4 — the arrows grow with the grade: (R →_k S) ≤ (R →_ℓ S) for k ≤ ℓ
-- statement:
--   For all search problems $R,S$ and $k\le\ell$ in $\mathbb N$,
--   $$(R\to_k S)\;\le\;(R\to_\ell S).$$
--
--   Differences from the source:
--   - encoding: Turing machines, polynomial time, and the encodings ⟨M⟩, ⟨x, y⟩ (no model fixed) → one concrete deterministic multi-tape Turing machine model (`Machine`, `Machine.evalWithin`, output on tape 0) with binary codes `Machine.encode`/`decode` and the pairing `pair x y` (bits of x doubled, then 01, then y); the bit b of ⟨x, b⟩ is the one-bit string [b]; reason: the paper fixes no model and its arguments only use that machines can be simulated, composed and padded with polynomial overhead, which holds in this model
-- source:
--   Ben-David, Ebtehaj, The Metacomplexity Structure of Search Problems, STOC 2027 submission (manuscript sha256 c3b015ea…), p. 23, Lemma 3.4

import Mathlib
import Definitions.Def_MetaSearch_Heyting_Machine
import Definitions.Def_MetaSearch_Heyting_SearchProblem
import Definitions.Def_MetaSearch_Heyting_JoinMeet
import Definitions.Def_MetaSearch_Heyting_Refutation
import Definitions.Def_MetaSearch_Heyting_Ideal

namespace MetaSearch.Heyting

theorem lemma_3_4 (R S : SearchProblem) (k l : ℕ) (hkl : k ≤ l) :
    Reduces (arrow k R S) (arrow l R S) := by sorry

end MetaSearch.Heyting
