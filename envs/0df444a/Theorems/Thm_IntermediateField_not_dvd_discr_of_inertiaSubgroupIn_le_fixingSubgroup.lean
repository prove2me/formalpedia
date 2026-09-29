-- Prove2me | Theorems.Thm_IntermediateField_not_dvd_discr_of_inertiaSubgroupIn_le_fixingSubgroup
-- name    : IntermediateField.not_dvd_discr_of_inertiaSubgroupIn_le_fixingSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/59abb5cf-66a2-5c50-b06e-2e7a83722919
-- title:
--   Trivial inertia above q implies q ∤ d_F
-- statement:
--   Let $F$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ (realised inside `AlgebraicClosure ℚ`) which is finite-dimensional over $\mathbb{Q}$ and Galois over $\mathbb{Q}$, and let $q$ be a prime natural number. Assume that for every valuation subring $P$ of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that the image of $q$ in $\overline{\mathbb{Q}}$ is a non-unit of $P$, the subgroup of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained as the image, under the inclusion of the decomposition subgroup of $P$ over $\mathbb{Q}$, of the inertia subgroup of $P$ over $\mathbb{Q}$ is contained in the fixing subgroup of $F$, i.e. in $\mathrm{Gal}(\overline{\mathbb{Q}}/F)$. Then, viewing $F$ as a number field (its finite-dimensionality over $\mathbb{Q}$ supplying the `NumberField` structure), the integer $q$ does not divide the discriminant $d_F$ of $F$.
--
--   This is one direction of the place-level form of Dedekind's discriminant theorem combined with Hilbert ramification theory: triviality of inertia at all places above $q$ forces $q$ to be unramified in $F$, hence coprime to $d_F$. It serves as the bridge from unramifiedness of a global Galois representation at $q$ to arithmetic statements about the fixed field, and is used in the construction of finite flat prolongations and in the verification of flatness conditions for $q$-adic Galois representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_not_dvd_discr_of_inertiaSubgroupIn_le_fixingSubgroup.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IntermediateField.not_dvd_discr_of_inertiaSubgroupIn_le_fixingSubgroup
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] [IsGalois ℚ F]
    (q : ℕ) (hq : q.Prime)
    (hunr : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
      P.inertiaSubgroupIn ℚ ≤ F.fixingSubgroup) :
    haveI : NumberField F := @NumberField.mk _ _ inferInstance ‹FiniteDimensional ℚ F›
    ¬ (q : ℤ) ∣ NumberField.discr F := by sorry
