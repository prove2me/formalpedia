-- Prove2me | Theorems.Thm_MazurTransfer_RelativeGroupLawInternalScalar_canonical_schemeNsmul
-- name    : MazurTransfer.RelativeGroupLawInternalScalar.canonical_schemeNsmul
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T04:37:17.283607+00:00
-- url     : https://prove2.me/theorems/7cd0139a-4200-41c5-ba75-5db0b6ad2ecd
-- title:
--   Scalar morphisms of the canonical relative group law
-- statement:
--   Let $R$ be a commutative ring and let $A$ be a scheme over $\operatorname{Spec}R$ equipped with an internal group structure. Let $G$ be the corresponding relative group law. For every natural number $n$, its scalar morphism is the underlying scheme morphism of the $n$th power of the identity in the internal point group:
--
--   $$[n]_G=(\operatorname{id}_A)^n.$$
--
--   This identifies scalar multiplication for the represented group law with the internal-group expression used by the actual rational norm maps.
-- source:
--   MazurTheorem, RelativeGroupLawInternalScalar.lean, original scalar compatibility theorem and complete induction helper; full source SHA-256 10d9e8c4695cb3bd258bd1174e90ce4055efd7f00eb4adf710b51e98c40e9172, Apache-2.0. Official Anthropic FLT interfaces at https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 .

import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj

theorem MazurTransfer.RelativeGroupLawInternalScalar.canonical_schemeNsmul {R : Type u} [CommRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) [GrpObj (Over.mk f)] (n : ℕ) :
    (relativeGroupLawOfGrpObj R f).schemeNsmul n =
      ((𝟙 (Over.mk f)) ^ n).left := by sorry
