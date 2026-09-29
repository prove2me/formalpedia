-- Prove2me | Theorems.Thm_IntermediateField_inertiaSubgroupIn_le_fixingSubgroup_of_not_dvd_discr
-- name    : IntermediateField.inertiaSubgroupIn_le_fixingSubgroup_of_not_dvd_discr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/6d843cd1-2bd0-5a47-9338-1dc8ea424785
-- title:
--   Inertia at q ∤ d_F fixes F pointwise
-- statement:
--   Let $F$ be an intermediate field of $\mathbb{Q}$ inside $\mathrm{AlgebraicClosure}\,\mathbb{Q}$ that is finite-dimensional over $\mathbb{Q}$, so that $F$ is a number field and its discriminant $\mathrm{NumberField.discr}\,F \in \mathbb{Z}$ is defined. Let $q$ be a prime natural number and assume that $q$, viewed in $\mathbb{Z}$, does not divide $\mathrm{NumberField.discr}\,F$. Let $P$ be a valuation subring of $\mathrm{AlgebraicClosure}\,\mathbb{Q}$ satisfying `P.LiesOverPrime q`, that is, the image of $q$ in the algebraic closure is a non-unit of $P$ (equivalently, $q$ lies in the maximal ideal of $P$, so the place $P$ lies above $q$). The conclusion is an inclusion of subgroups of $\mathrm{Aut}(\mathrm{AlgebraicClosure}\,\mathbb{Q}/\mathbb{Q})$: the group `P.inertiaSubgroupIn ℚ`, defined as the image under the inclusion of the decomposition subgroup of $P$ over $\mathbb{Q}$ of the inertia subgroup of $P$ over $\mathbb{Q}$, is contained in `F.fixingSubgroup`, the subgroup of those $\mathbb{Q}$-automorphisms of the algebraic closure which fix every element of $F$. In words: every element of the inertia group at a place above an unramified prime $q$ acts trivially on $F$.
--
--   This is the "discriminant implies inertia" half of the standard dictionary between unramifiedness of a rational prime in a number field (Dedekind's discriminant theorem) and triviality of inertia on that field (Hilbert ramification theory in towers), formulated for places of a fixed algebraic closure of $\mathbb{Q}$. It is used to verify that a Galois representation is unramified outside a prescribed set of primes, as in [`Rep.dualTwist_cycloChar_unramifiedOutside`](thm.html#Rep.dualTwist_cycloChar_unramifiedOutside).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_inertiaSubgroupIn_le_fixingSubgroup_of_not_dvd_discr.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IntermediateField.inertiaSubgroupIn_le_fixingSubgroup_of_not_dvd_discr
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F]
    (q : ℕ) (hq : q.Prime)
    (hdisc : haveI : NumberField F := @NumberField.mk _ _ inferInstance ‹FiniteDimensional ℚ F›;
             ¬ (q : ℤ) ∣ NumberField.discr F)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q) :
    P.inertiaSubgroupIn ℚ ≤ F.fixingSubgroup := by sorry
