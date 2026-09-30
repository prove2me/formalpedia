-- Prove2me | Theorems.Thm_LocalConjugacy_theorem_1_1
-- name    : LocalConjugacy.theorem_1_1
-- status  : Open
-- author  : @burkh4rt
-- created : 2026-09-30T03:54:09.610663+00:00
-- url     : https://prove2.me/theorems/5e33e708-d08c-4180-8777-dfc5cb568937
-- title:
--   Theorem 1.1
-- statement:
--   Let $N$ be a pronilpotent normal closed subgroup of a profinite group $G$. If either $G$ is prosupersolvable or $G/N$ is pronilpotent, then two closed supplements of $N$ are conjugate if and only if they are locally conjugate.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, arXiv:2609.37678v1 (29 September 2026), https://arxiv.org/pdf/2609.37678v1, p. 1, Theorem 1.1; standing conventions in §1.2, pp. 2–3.

import Definitions.Def_LocalConjugacy_Groups

/-
Theorem 1.1: no finiteness or bounded nilpotency-class hypothesis is imposed on N.
The supplements and the normal pronilpotent subgroup are closed.

This is an open draft target. The deliberate `sorry` is the target proof hole;
all definitions and the structural proofs on which the statement rests compile
without admitted proofs.
-/
universe u v
open LocalConjugacy

theorem LocalConjugacy.theorem_1_1 {G : ProfiniteGrp.{u}} (N H K : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
    (hK : IsClosed (K : Set G)) (hpron : Pronilpotent N)
    (hcase : Prosupersolvable G ∨ Pronilpotent (G ⧸ N))
    (hHN : Supplements N H) (hKN : Supplements N K) :
    Conjugate H K ↔ LocallyConjugate H K := by sorry
