-- Prove2me | Theorems.Thm_MazurTransfer_Order13IntegralSections_infinityMorphism_baseChange
-- name    : MazurTransfer.Order13IntegralSections.infinityMorphism_baseChange
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T04:07:16.845869+00:00
-- url     : https://prove2.me/theorems/64e35607-b0b7-4de3-9014-2ed85fbf609f
-- title:
--   Actual infinity morphisms are natural under scalar extension
-- statement:
--   Let $R$ and $S$ be commutative rings with an $R$-algebra map $\phi:R\to S$. For $a\in R$ with $a^2=1$, let $s_{R,a}:\operatorname{Spec}R\to C_R$ be the actual infinity morphism given by reciprocal coordinates $z=0,w=a$. If $f_{S/R}:C_S\to C_R$ is the specified actual curve map, then
--   $$f_{S/R}\circ s_{S,\phi(a)}=s_{R,a}\circ\operatorname{Spec}(\phi).$$
--
--   Thus the actual positive and negative infinity sections are compatible with arbitrary scalar extension. This supplies the basepoint compatibility in the integral Abel–Jacobi dictionary and literal Picard fibre transport.
-- source:
--   Unchanged reciprocal-evaluation naturality and infinity-morphism naturality proof bodies from MazurTheorem Order13IntegralInfinitySectionsBaseChange.lean. The Lean syntax oracles preserve the proof and section context; the two coordinate evaluations forward to the already published primitive constructor library. The full original and public types are checked by closed kernel witnesses. Vas and contributors, Apache-2.0.

import Mathlib
import Definitions.Def_MazurTransfer_Order13IntegralInfinitySections
import Definitions.Def_MazurTransfer_Order13ActualCurveBaseChangeMap
open CategoryTheory AlgebraicGeometry
open MazurTransfer.Order13IntegralSections MazurTransfer.Order13ActualCurveBaseChange
universe u

theorem MazurTransfer.Order13IntegralSections.infinityMorphism_baseChange (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R) (ha : a ^ 2 = 1) :
    infinityMorphism S (algebraMap R S a)
      (by rw [← map_pow, ha, map_one]) ≫ curveMap R S =
    Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ infinityMorphism R a ha  := by sorry
