-- Prove2me | Theorems.Thm_LocalConjugacy_proposition_3_2
-- name    : LocalConjugacy.proposition_3_2
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T12:47:14.872347+00:00
-- url     : https://prove2.me/theorems/9df64b26-0eed-493a-bf39-654237532eda
-- title:
--   Proposition 3.2
-- statement:
--   If $N$ is finite, Theorem 1.1 holds.
--
--   Explicitly, let $N$ be a finite closed normal pronilpotent subgroup of a profinite group $G$. If either $G$ is prosupersolvable or $G/N$ is pronilpotent, then any two closed supplements of $N$ are conjugate if and only if they are locally conjugate.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, arXiv:2609.37678v1 (29 September 2026), https://arxiv.org/pdf/2609.37678v1, p. 6, Proposition 3.2; standing conventions in §1.2, pp. 2–3.

import Definitions.Def_LocalConjugacy_Groups

/-
Proposition 3.2: the complete statement of Theorem 1.1 with finite N.
The ambient profinite group G is not assumed finite.

This is an open draft target. The deliberate `sorry` is the target proof hole;
all definitions and the structural proofs on which the statement rests compile
without admitted proofs.
-/
universe u v
open LocalConjugacy

theorem LocalConjugacy.proposition_3_2 {G : ProfiniteGrp.{u}} (N H K : Subgroup G) [N.Normal] [Finite N]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
    (hK : IsClosed (K : Set G)) (hpron : Pronilpotent N)
    (hcase : Prosupersolvable G ∨ Pronilpotent (G ⧸ N))
    (hHN : Supplements N H) (hKN : Supplements N K) :
    Conjugate H K ↔ LocallyConjugate H K := by sorry
