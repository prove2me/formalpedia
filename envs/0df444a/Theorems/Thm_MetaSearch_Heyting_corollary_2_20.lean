-- Prove2me | Theorems.Thm_MetaSearch_Heyting_corollary_2_20
-- name    : MetaSearch.Heyting.corollary_2_20
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:23:39.439496+00:00
-- url     : https://prove2.me/theorems/c76ebb17-c4e3-44a2-b464-8fb2fae157e8
-- title:
--   Corollary 2.20 — the ideal completion of Verifiable is a complete Heyting algebra with bottom FP, whose elements are the complexity classes
-- statement:
--   Let `IdealClass` be the set of ideals of $(\mathsf{Verifiable},\le)$. Then:
--   1. there is a **frame** structure (complete lattice that is a Heyting algebra, `Order.Frame`) on the ideals whose order is inclusion, $I\le J\iff I\subseteq J$, and whose bottom element is $\mathsf{FP}$;
--   2. a set $I$ of search problems is an ideal iff $I\subseteq\mathsf{Verifiable}$, $I\neq\emptyset$, $I$ is downward closed under mapping reductions within $\mathsf{Verifiable}$, and $I$ is closed under finite joins (every finite $\vee$-join of members, the empty join $\mathsf{triv}$ included, lies in $I$).
--
--   This identifies complexity classes of verifiable search problems with the elements of a complete Heyting algebra.
--
--   Differences from the source:
--   - encoding: 'The ideal completion of Verifiable is a complete Heyting algebra (also known as a frame or locale)', 'The bottom element of this completion is the ideal FP' → there exists an `Order.Frame` on `IdealClass` (ideals as a structure, no order of its own) whose order is `I ≤ J ↔ I.carrier ⊆ J.carrier` and whose `⊥` has carrier FP; reason: a complete Heyting algebra is a frame, and the ideal completion is the set of ideals ordered by ⊆ (p. 20); the order pins the frame down
--   - encoding: 'Its elements (the ideals of Verifiable) correspond to complexity classes … each of these is a nonempty set of polytime verifiable search problems which is downwards closed under mapping reductions and closed under finite joins' → `IsIdeal I ↔ (I ⊆ Verifiable ∧ I.Nonempty ∧ lower set within Verifiable ∧ JoinClosure-closed)`; reason: the correspondence is that the ideals are exactly those sets
--   - encoding: 'closed under finite joins of search problems' → every member of `JoinClosure I` (generated from I by triv and binary ∨) lies in I; reason: a finite join is an iterated binary join; the empty join is the bottom triv (p. 3)
--   - encoding: Turing machines, polynomial time, and the encodings ⟨M⟩, ⟨x, y⟩ (no model fixed) → one concrete deterministic multi-tape Turing machine model (`Machine`, `Machine.evalWithin`, output on tape 0) with binary codes `Machine.encode`/`decode` and the pairing `pair x y` (bits of x doubled, then 01, then y); the bit b of ⟨x, b⟩ is the one-bit string [b]; reason: the paper fixes no model and its arguments only use that machines can be simulated, composed and padded with polynomial overhead, which holds in this model
-- source:
--   Ben-David, Ebtehaj, The Metacomplexity Structure of Search Problems, STOC 2027 submission (manuscript sha256 c3b015ea…), p. 21, Corollary 2.20

import Mathlib
import Definitions.Def_MetaSearch_Heyting_Machine
import Definitions.Def_MetaSearch_Heyting_SearchProblem
import Definitions.Def_MetaSearch_Heyting_JoinMeet
import Definitions.Def_MetaSearch_Heyting_Refutation
import Definitions.Def_MetaSearch_Heyting_Ideal

namespace MetaSearch.Heyting

theorem corollary_2_20 :
    (∃ _ : Order.Frame IdealClass,
      (∀ I J : IdealClass, I ≤ J ↔ I.carrier ⊆ J.carrier) ∧ (⊥ : IdealClass).carrier = FP) ∧
    (∀ I : Set SearchProblem, IsIdeal I ↔
      (I ⊆ Verifiable ∧ I.Nonempty ∧
        (∀ R S, R ∈ Verifiable → Reduces R S → S ∈ I → R ∈ I) ∧
        ∀ S, JoinClosure I S → S ∈ I)) := by sorry

end MetaSearch.Heyting
