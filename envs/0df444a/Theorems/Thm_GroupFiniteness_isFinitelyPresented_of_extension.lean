-- Prove2me | Theorems.Thm_GroupFiniteness_isFinitelyPresented_of_extension
-- name    : GroupFiniteness.isFinitelyPresented_of_extension
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-20T08:54:07.19044+00:00
-- url     : https://prove2.me/theorems/2dd88035-26b5-4361-81ce-14cc2e0e7104
-- title:
--   An extension of a finitely presented group by a finitely presented group is finitely presented
-- statement:
--   Let $N$ be a normal subgroup of a group $G$ such that both $N$ and the quotient $G/N$ are
--   finitely presented. Then $G$ is finitely presented.
--
--   A presentation of $G$ is obtained from generators of $N$ together with lifts of generators of
--   $G/N$, with relations: the relations of $N$, the relations of $G/N$ read as words that land in $N$
--   and then expressed in the generators of $N$, and the conjugation relations expressing
--   $x n x^{-1}$ in the generators of $N$ for each generator $x$ of the lift and each generator $n$
--   of $N$.
--
--   The weaker-looking hypothesis that $N$ is merely finitely *generated* and $G/N$ finitely presented
--   does not suffice: taking $N = G$ would make every finitely generated group finitely presented.
-- source:
--   Standard; due to P. Hall, Finiteness conditions for soluble groups, Proceedings of the London Mathematical Society s3-4 (1954) 419–436, https://doi.org/10.1112/plms/s3-4.1.419, where finite presentability of such extensions is part of the finiteness-condition theory. The statement here is the general group-theoretic fact, not a result of any one paper of the missions this was developed for.

import Mathlib

namespace GroupFiniteness

/-- P. Hall: an extension of a finitely presented group by a finitely presented group is finitely
presented. Note that the weaker-looking hypothesis "`N` finitely generated and `G ⧸ N` finitely
presented" does **not** suffice: taking `N = G` would make every finitely generated group finitely
presented. -/
theorem isFinitelyPresented_of_extension {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    [Group.IsFinitelyPresented N] [Group.IsFinitelyPresented (G ⧸ N)] :
    Group.IsFinitelyPresented G := by
  sorry

end GroupFiniteness
