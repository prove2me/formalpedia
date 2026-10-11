-- Prove2me | Theorems.Thm_MazurTransfer_proper_valuation_point_restriction_bijective
-- name    : MazurTransfer.proper_valuation_point_restriction_bijective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T12:13:57.040326+00:00
-- url     : https://prove2.me/theorems/e17ae446-db23-4740-82d6-a95c1bb44f03
-- title:
--   Unique extension of proper points over a valuation ring
-- statement:
--   Let $X$ be proper over $\operatorname{Spec}R$, let $B$ be an integral valuation ring with fraction field $K$, and fix a morphism $t\colon\operatorname{Spec}B\to\operatorname{Spec}R$. Restriction along $\operatorname{Spec}K\to\operatorname{Spec}B$ is a bijection from $B$-valued points of $X$ over $t$ to $K$-valued points over the composite base map. Thus every fraction-field point extends uniquely to a point over the valuation ring. This is used to construct the actual rational-to-finite-field specialization maps for the integral order-13 Picard family.
-- source:
--   Mathlib pinned at 0df444a360eaa60ab8c11dca51a86af692955474, Mathlib/AlgebraicGeometry/ValuativeCriterion.lean, IsProper.eq_valuativeCriterion; relative points from official Anthropic FLT pin 6e837e75355538c7f80bab5b956861e86c4eacc2.

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

universe u
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem MazurTransfer.proper_valuation_point_restriction_bijective
    (R : Type u) [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (B K : Type u) [CommRing B] [IsDomain B] [ValuationRing B]
    [Field K] [Algebra B K] [IsFractionRing B K]
    (t : Spec (.of B) ⟶ Spec (.of R)) :
    Function.Bijective (schemeHomOverComp (t := t) (f := f)
      (Spec.map (CommRingCat.ofHom (algebraMap B K))) rfl) := by sorry
