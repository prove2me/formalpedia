-- Prove2me | Theorems.Thm_LocalConjugacy_proposition_3_1
-- name    : LocalConjugacy.proposition_3_1
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T12:43:49.780271+00:00
-- url     : https://prove2.me/theorems/9459dbff-6cac-4aa2-95bc-d0c4a297898e
-- title:
--   Proposition 3.1
-- statement:
--   Given $N$ and $G$ satisfying the hypotheses of Theorem 1.1 where $N$ is finite, two closed complements of $N$ are conjugate if and only if they are locally conjugate.
--
--   Here Theorem 1.1 requires that $G$ be profinite, $N$ be a closed normal pronilpotent subgroup, and either $G$ be prosupersolvable or $G/N$ be pronilpotent. This proposition additionally requires $N$ finite and both subgroups to be closed complements of $N$.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, arXiv:2609.37678v1 (29 September 2026), https://arxiv.org/pdf/2609.37678v1, p. 6, Proposition 3.1; standing conventions in §1.2, pp. 2–3.

import Definitions.Def_LocalConjugacy_Groups

/-
Proposition 3.1: in the arXiv version N is finite. Both H and K are actual
complements, expressed with Mathlib’s standard subgroup complement predicate.

This is an open draft target. The deliberate `sorry` is the target proof hole;
all definitions and the structural proofs on which the statement rests compile
without admitted proofs.
-/
universe u v
open LocalConjugacy

theorem LocalConjugacy.proposition_3_1 {G : ProfiniteGrp.{u}} (N H K : Subgroup G) [N.Normal] [Finite N]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
    (hK : IsClosed (K : Set G)) (hpron : Pronilpotent N)
    (hcase : Prosupersolvable G ∨ Pronilpotent (G ⧸ N))
    (hNH : N.IsComplement' H) (hNK : N.IsComplement' K) :
    Conjugate H K ↔ LocallyConjugate H K := by sorry
