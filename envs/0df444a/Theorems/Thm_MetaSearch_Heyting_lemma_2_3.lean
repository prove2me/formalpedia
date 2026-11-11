-- Prove2me | Theorems.Thm_MetaSearch_Heyting_lemma_2_3
-- name    : MetaSearch.Heyting.lemma_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:23:49.933551+00:00
-- url     : https://prove2.me/theorems/4af71667-d64b-4767-9d5b-b29b8c86b906
-- title:
--   Lemma 2.3 — the bottom elements of Search are the polynomial-time solvable problems; within Verifiable they form FP
-- statement:
--   Let $\le$ be mapping reducibility between search problems. A search problem $S$ is a **bottom element** of $(\mathsf{Search},\le)$ if $S\le T$ for every search problem $T$. The lemma says:
--   $$S\le T\ \text{for all } T\iff \exists\,A \text{ polynomial-time computable with } (x,A(x))\in S\ \text{for all }x,$$
--   and the bottom elements of $(\mathsf{Verifiable},\le)$ form exactly $\mathsf{FP}$:
--   $$\{S\in\mathsf{Verifiable}: S\le T\text{ for all }T\in\mathsf{Verifiable}\}=\mathsf{FP}.$$
--   This identifies $\mathsf{FP}$ as the bottom of the ideal completion.
--
--   Differences from the source:
--   - encoding: Turing machines, polynomial time, and the encodings ⟨M⟩, ⟨x, y⟩ (no model fixed) → one concrete deterministic multi-tape Turing machine model (`Machine`, `Machine.evalWithin`, output on tape 0) with binary codes `Machine.encode`/`decode` and the pairing `pair x y` (bits of x doubled, then 01, then y); the bit b of ⟨x, b⟩ is the one-bit string [b]; reason: the paper fixes no model and its arguments only use that machines can be simulated, composed and padded with polynomial overhead, which holds in this model
-- source:
--   Ben-David, Ebtehaj, The Metacomplexity Structure of Search Problems, STOC 2027 submission (manuscript sha256 c3b015ea…), p. 17, Lemma 2.3

import Mathlib
import Definitions.Def_MetaSearch_Heyting_Machine
import Definitions.Def_MetaSearch_Heyting_SearchProblem
import Definitions.Def_MetaSearch_Heyting_JoinMeet
import Definitions.Def_MetaSearch_Heyting_Refutation
import Definitions.Def_MetaSearch_Heyting_Ideal

namespace MetaSearch.Heyting

theorem lemma_2_3 :
    (∀ S : SearchProblem, (∀ T : SearchProblem, Reduces S T) ↔
      ∃ A : List Bool → List Bool, PolyTimeFun A ∧ ∀ x, (x, A x) ∈ S) ∧
    {S : SearchProblem | S ∈ Verifiable ∧ ∀ T ∈ Verifiable, Reduces S T} = FP := by sorry

end MetaSearch.Heyting
