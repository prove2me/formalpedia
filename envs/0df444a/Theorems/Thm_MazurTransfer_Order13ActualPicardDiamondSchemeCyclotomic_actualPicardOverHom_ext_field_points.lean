-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualPicardDiamondSchemeCyclotomic_actualPicardOverHom_ext_field_points
-- name    : MazurTransfer.Order13ActualPicardDiamondSchemeCyclotomic.actualPicardOverHom_ext_field_points
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T20:13:54.066201+00:00
-- url     : https://prove2.me/theorems/81647404-8c22-4640-a87a-08923850ed08
-- title:
--   Endomorphisms of the actual rational Picard scheme are determined by perfect characteristic-zero field points
-- statement:
--   Let P be the same actual rational represented Picard scheme of the order-thirteen curve. Let f and g be endomorphisms of P over Q. If for every perfect characteristic-zero field K and every K-valued point a of P one has
--
--   $$f\circ a=g\circ a,$$
--
--   then f=g as morphisms over Q. This is the field-point comparison used to promote the geometric diamond and nineteen-norm identities to genuine scheme identities.
-- source:
--   Original MazurTheorem Order13ActualPicardDiamondSchemeCyclotomic.actualPicardOverHom_ext_field_points, retaining the same rational Picard family and exact original full type. The smooth, reduced and separated geometry is taken from that same actual integral family. Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: endomorphisms of the SAME actual rational Picard are
determined by every perfect characteristic-zero field point.
Named downstream consumer: genuine diamond cyclotomic and nineteen-norm
scheme identities. Original MazurTheorem field-point extensionality bridge.
-/
import Definitions.Def_MazurTransfer_Order13ActualPicardReducedProperGeometryData
import Theorems.Thm_MazurTransfer_RationalSchemeMorphismFieldPointExtensionality_hom_eq_of_field_points
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra GoodReductionJacobian
open MazurTransfer.Order13ActualPicardDiamondSchemeEndomorphism
open MazurTransfer.Order13ActualPicardReducedProperGeometry

theorem MazurTransfer.Order13ActualPicardDiamondSchemeCyclotomic.actualPicardOverHom_ext_field_points
    (f g : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase)
    (H : ∀ (K : Type) [Field K] [CharZero K] [PerfectField K]
      (a : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ K))) ⟶ Over.mk actualPicard.toBase),
        a ≫ f = a ≫ g) : f = g := by sorry
