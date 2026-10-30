-- Prove2me | Theorems.Thm_MITMSynthesis_star_mem_S_iff
-- name    : MITMSynthesis.star_mem_S_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:06:28.62972+00:00
-- url     : https://prove2.me/theorems/9118f253-e48a-4062-8294-fb07387b0a62
-- title:
--   Lemma 1, preliminary claim: $U \in S_i^\dagger$ iff $U \in S_i$
-- statement:
--   Let $\mathcal G$ be an instruction set (closed under inverses), $n \in \mathbb N$, and let $S_i$ be the set of $n$-qubit unitaries implementable in depth $i$ over $\mathcal G$. For every $i$ and every $2^n\times 2^n$ matrix $U$,
--
--   $$
--   U \in S_i^\dagger = \{\, W^\dagger : W \in S_i \,\} \iff U \in S_i .
--   $$
--
--   This is the claim proved at the start of the proof of Lemma 1: the set of depth-$i$ unitaries is closed under taking adjoints.
--
--   Differences from the source:
--   - reading: U can be implemented in depth i over G → U ∈ S_i, a product of exactly i elements of V_{n,G}; reason: the paper's S_i ("the set of all unitaries implementable in depth i") is built as S_0 = {I}, S_i = V_{n,G}S_{i−1} on p. 6, i.e. products of exactly i elements
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, proof of Lemma 1, p. 5 ("U ∈ S_i† = {U†|U ∈ S_i} if and only if U can be implemented in depth i over G")

import Mathlib
import Definitions.Def_MITMSynthesis_Gate
import Definitions.Def_MITMSynthesis_depthOneSet
import Definitions.Def_MITMSynthesis_S

namespace MITMSynthesis

/-- **Lemma 1, preliminary claim.** Amy–Maslov–Mosca–Roetteler, arXiv:1206.0758v3, proof of
Lemma 1, p. 5: "U ∈ S_i† = {U† | U ∈ S_i} if and only if U can be implemented in depth i over G."
For an instruction set `G` (closed under inverses) and every depth `i`, `U ∈ S_i†` iff `U ∈ S_i`. -/
theorem star_mem_S_iff {n : ℕ} {G : Set Gate} (hG : IsInstructionSet G) (i : ℕ)
    (U : Matrix (Q n) (Q n) ℂ) :
    U ∈ star '' S (depthOneSet n G) i ↔ U ∈ S (depthOneSet n G) i := by sorry

end MITMSynthesis
