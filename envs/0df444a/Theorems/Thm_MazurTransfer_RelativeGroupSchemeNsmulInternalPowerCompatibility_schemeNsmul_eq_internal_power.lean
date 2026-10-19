-- Prove2me | Theorems.Thm_MazurTransfer_RelativeGroupSchemeNsmulInternalPowerCompatibility_schemeNsmul_eq_internal_power
-- name    : MazurTransfer.RelativeGroupSchemeNsmulInternalPowerCompatibility.schemeNsmul_eq_internal_power
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T20:34:50.264739+00:00
-- url     : https://prove2.me/theorems/06d5c26d-2583-4ccc-8159-5b649c7e2d44
-- title:
--   Relative group-law multiplication by n equals the underlying internal power of the identity
-- statement:
--   Let a scheme over a commutative ring carry an internal group object structure in the over category. The relative group-law multiplication-by-n scheme morphism is the underlying scheme morphism of the nth pointwise power of its identity morphism. This retains the original complete universes and arbitrary commutative base ring. The named downstream consumer is converting the actual Picard norm composites into multiplication by nineteen.
-- source:
--   Complete original MazurTheorem RelativeGroupSchemeNsmulInternalPowerCompatibility.schemeNsmul_eq_internal_power and its original pointwise power helper, using the official Anthropic FLT relative group-law interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: integer multiplication in the relative group-law API is
exactly the underlying morphism of the internal pointwise power of the
identity. Named downstream consumer: formal unramifiedness of the actual
Picard norm factors via their checked scalar-nineteen composites.
-/
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped CategoryTheory.MonObj
variable {R : Type u} [CommRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) [GrpObj (Over.mk f)]

theorem MazurTransfer.RelativeGroupSchemeNsmulInternalPowerCompatibility.schemeNsmul_eq_internal_power (n : ℕ) :
    (relativeGroupLawOfGrpObj R f).schemeNsmul n = ((𝟙 (Over.mk f)) ^ n).left := by sorry
