-- Prove2me | Theorems.Thm_Matrix_SpecialLinearGroup_card_sylow_eq_card_add_one_of_finite
-- name    : Matrix.SpecialLinearGroup.card_sylow_eq_card_add_one_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/e22b6b85-a0cd-5071-9624-5662a240bb8b
-- title:
--   Number of Sylow p-subgroups of a finite subgroup of SL₂(K)
-- statement:
--   Let $K$ be a field of characteristic $p$, where $p$ is a prime with $p \neq 2$, let $G$ be a subgroup of $\mathrm{SL}_2(K)$ which is finite, and let $P$ be a Sylow $p$-subgroup of $G$. Assume that the cardinality of $P$ exceeds $3$, and that the number of Sylow $p$-subgroups of $G$ is not equal to $1$, i.e. $P$ is not normal in $G$. Then the number of Sylow $p$-subgroups of $G$ equals $\operatorname{card} P + 1$. All cardinalities are natural-number cardinalities, so the hypothesis $3 < \operatorname{card} P$ says that the order of the Sylow $p$-subgroup, necessarily a power $q$ of $p$, satisfies $q > 3$, and the conclusion is the equality $n_p(G) = q + 1$.
--
--   This is the counting step in Dickson's classification of the finite subgroups of $\mathrm{SL}_2$ over a field of odd characteristic: a finite subgroup whose Sylow $p$-subgroups are non-normal of order $q>3$ has exactly $q+1$ of them, the situation of $\mathrm{SL}_2(\mathbb{F}_q)$ acting doubly transitively on the projective line. It is used in the construction of a subfield over which the unipotent subgroup is defined, via [`Matrix.SpecialLinearGroup.exists_subfield_forall_upperElem_mem_iff_of_finite`](thm.html#Matrix.SpecialLinearGroup.exists_subfield_forall_upperElem_mem_iff_of_finite).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_SpecialLinearGroup_card_sylow_eq_card_add_one_of_finite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix MatrixGroups

theorem Matrix.SpecialLinearGroup.card_sylow_eq_card_add_one_of_finite
    {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (G : Subgroup SL(2, K)) [Finite G] (P : Sylow p G)
    (hq : 3 < Nat.card P) (hP : Nat.card (Sylow p G) ≠ 1) :
    Nat.card (Sylow p G) = Nat.card P + 1 := by sorry
