-- Prove2me | Theorems.Thm_MetaSearch_Heyting_lemma_3_8
-- name    : MetaSearch.Heyting.lemma_3_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:23:55.895527+00:00
-- url     : https://prove2.me/theorems/4d280ecb-43ad-4508-9e09-6c72b96fa0f8
-- title:
--   Lemma 3.8 — for k ≥ 2, refuting an algorithm is equivalent to refuting a reduction to triv: ¬_k S ≡ S →_k triv
-- statement:
--   Let $S$ be any search problem and $k\ge2$. Then $\neg_k S$ and $S\to_k\mathsf{triv}$ reduce to each other:
--   $$\neg_k S\le S\to_k\mathsf{triv}\qquad\text{and}\qquad S\to_k\mathsf{triv}\le\neg_k S,$$
--   with the same grade $k$ on both sides.
--
--   Differences from the source:
--   - reading: '¬_kS is equivalent to S →_k triv' → reductions in both directions, `Reduces (neg k S) (arrow k S triv) ∧ Reduces (arrow k S triv) (neg k S)`; reason: equivalence in a preorder is mutual reducibility; the proof gives both reductions
--   - encoding: Turing machines, polynomial time, and the encodings ⟨M⟩, ⟨x, y⟩ (no model fixed) → one concrete deterministic multi-tape Turing machine model (`Machine`, `Machine.evalWithin`, output on tape 0) with binary codes `Machine.encode`/`decode` and the pairing `pair x y` (bits of x doubled, then 01, then y); the bit b of ⟨x, b⟩ is the one-bit string [b]; reason: the paper fixes no model and its arguments only use that machines can be simulated, composed and padded with polynomial overhead, which holds in this model
-- source:
--   Ben-David, Ebtehaj, The Metacomplexity Structure of Search Problems, STOC 2027 submission (manuscript sha256 c3b015ea…), pp. 25-26, Lemma 3.8

import Mathlib
import Definitions.Def_MetaSearch_Heyting_Machine
import Definitions.Def_MetaSearch_Heyting_SearchProblem
import Definitions.Def_MetaSearch_Heyting_JoinMeet
import Definitions.Def_MetaSearch_Heyting_Refutation
import Definitions.Def_MetaSearch_Heyting_Ideal

namespace MetaSearch.Heyting

theorem lemma_3_8 (S : SearchProblem) (k : ℕ) (hk : 2 ≤ k) :
    Reduces (neg k S) (arrow k S triv) ∧ Reduces (arrow k S triv) (neg k S) := by sorry

end MetaSearch.Heyting
