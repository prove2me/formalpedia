-- Prove2me | Theorems.Thm_LocalConjugacy_proposition_4_1
-- name    : LocalConjugacy.proposition_4_1
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T12:50:57.308653+00:00
-- url     : https://prove2.me/theorems/f1f6567b-89e3-4545-878c-6869fa05017c
-- title:
--   Proposition 4.1
-- statement:
--   In a profinite group $G$, suppose $H,H'\leq G$ each supplement some abelian $N\trianglelefteq G$. If for each prime $p$, $H$ contains a conjugate of some Sylow $p$-subgroup of $H'$, then $H$ contains a conjugate of $H'$.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, arXiv:2609.37678v1 (29 September 2026), https://arxiv.org/pdf/2609.37678v1, p. 7, Proposition 4.1; standing conventions in §1.2, pp. 2–3.

import Definitions.Def_LocalConjugacy_Groups

/-
Proposition 4.1: the abelian subgroup N and both supplements are closed.
No solvability assumption is made on G.

This is an open draft target. The deliberate `sorry` is the target proof hole;
all definitions and the structural proofs on which the statement rests compile
without admitted proofs.
-/
universe u v
open LocalConjugacy

theorem LocalConjugacy.proposition_4_1 {G : ProfiniteGrp.{u}} (N H K : Subgroup G) [N.Normal]
    (hN : IsClosed (N : Set G)) (hH : IsClosed (H : Set G))
    (hK : IsClosed (K : Set G)) [IsMulCommutative N]
    (hHN : Supplements N H) (hKN : Supplements N K)
    (hlocal : LocallyContains H K) : ∃ g : G, conjugate g K ≤ H := by sorry
