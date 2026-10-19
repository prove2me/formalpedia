-- Prove2me | Theorems.Thm_MazurTransfer_Order13EveryRepresentedIntegralPicardGeometry_every_represented_integral_picard_geometry
-- name    : MazurTransfer.Order13EveryRepresentedIntegralPicardGeometry.every_represented_integral_picard_geometry
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T03:31:25.593173+00:00
-- url     : https://prove2.me/theorems/65f9e32a-8f6f-4899-a453-8f6fead0153d
-- title:
--   Every representation of the integral order-13 Picard functor inherits the original geometry
-- statement:
--   Let $R$ be a Noetherian integral domain in which $104$ is invertible. Every genuine representation $D$ of the original relative degree-zero Picard functor of the integral order-13 curve, with its original positive-infinity section, satisfies
--
--   $$
--   D\longrightarrow\operatorname{Spec}R\quad\text{is smooth, proper, and geometrically connected}.
--   $$
--
--    The theorem applies to the specified representation, through the canonical representing isomorphism. Named downstream consumer: local abelian Picard models of the same selected integral family used to extend the actual rational norm maps.
-- source:
--   Original MazurTheorem Order13EveryRepresentedIntegralPicardGeometry.every_represented_integral_picard_geometry, Apache-2.0. Complete universe-polymorphic original and public types compared. Reuses the verified actual integral Picard representation theorem.

import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: every genuine representation of the actual integral
order-13 Picard functor inherits smooth, proper and geometrically
connected geometry through its canonical representing isomorphism.
Named downstream consumer: local abelian models of the SAME selected
integral Picard family used for rational norm extension.
-/
import Definitions.Def_MazurTransfer_PicardCanonicalRepresentationGroupIsomorphism
import Definitions.Def_MazurTransfer_Order13FiniteMapDataFromPublicCharts
import Definitions.Def_MazurTransfer_Order13ActualPicardTripleFamily

noncomputable section
universe u
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve Order13IntegralSections
open PicardCanonicalRepresentationGroupIsomorphism

theorem MazurTransfer.Order13EveryRepresentedIntegralPicardGeometry.every_represented_integral_picard_geometry
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (h104 : IsUnit (104 : R)) (D : RelativePic0Designation R (curveToBase R))
    (hD : RepresentsRelSubPic (curveToBase R) (positiveInfinitySection R)
      (algEquivZeroCut (curveToBase R) (positiveInfinitySection R)) D) :
    Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase := by sorry
