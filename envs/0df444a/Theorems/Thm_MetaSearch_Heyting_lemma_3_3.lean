-- Prove2me | Theorems.Thm_MetaSearch_Heyting_lemma_3_3
-- name    : MetaSearch.Heyting.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:23:55.912193+00:00
-- url     : https://prove2.me/theorems/df5060eb-f916-46a3-9031-77db83a40463
-- title:
--   Lemma 3.3 — R →_k S is verifiable when R and S are
-- statement:
--   For search problems $R,S$ and every $k\in\mathbb N$ (Definition 3.2 gives $R\to_k S$):
--   $$R,S\in\mathsf{Verifiable}\;\Longrightarrow\;(R\to_k S)\in\mathsf{Verifiable}.$$
--
--   Differences from the source:
--   - encoding: Turing machines, polynomial time, and the encodings ⟨M⟩, ⟨x, y⟩ (no model fixed) → one concrete deterministic multi-tape Turing machine model (`Machine`, `Machine.evalWithin`, output on tape 0) with binary codes `Machine.encode`/`decode` and the pairing `pair x y` (bits of x doubled, then 01, then y); the bit b of ⟨x, b⟩ is the one-bit string [b]; reason: the paper fixes no model and its arguments only use that machines can be simulated, composed and padded with polynomial overhead, which holds in this model
-- source:
--   Ben-David, Ebtehaj, The Metacomplexity Structure of Search Problems, STOC 2027 submission (manuscript sha256 c3b015ea…), p. 23, Lemma 3.3

import Mathlib
import Definitions.Def_MetaSearch_Heyting_Machine
import Definitions.Def_MetaSearch_Heyting_SearchProblem
import Definitions.Def_MetaSearch_Heyting_JoinMeet
import Definitions.Def_MetaSearch_Heyting_Refutation
import Definitions.Def_MetaSearch_Heyting_Ideal

namespace MetaSearch.Heyting

theorem lemma_3_3 (R S : SearchProblem) (hR : R ∈ Verifiable) (hS : S ∈ Verifiable)
    (k : ℕ) : arrow k R S ∈ Verifiable := by sorry

end MetaSearch.Heyting
