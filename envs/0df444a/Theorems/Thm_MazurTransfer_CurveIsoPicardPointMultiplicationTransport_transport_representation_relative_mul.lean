-- Prove2me | Theorems.Thm_MazurTransfer_CurveIsoPicardPointMultiplicationTransport_transport_representation_relative_mul
-- name    : MazurTransfer.CurveIsoPicardPointMultiplicationTransport.transport_representation_relative_mul
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T08:03:15.533717+00:00
-- url     : https://prove2.me/theorems/c6d04846-3cfa-4b4e-922d-a6972872b29c
-- title:
--   Pointed curve isomorphisms preserve the canonical relative Picard multiplication
-- statement:
--   Let $e:C^{\prime}\simeq C$ be an isomorphism over a commutative ring $R$ that respects specified sections. Let a designation $D$ represent the algebraically trivial rigidified relative Picard subfunctor for $C$, and transport that representation to $C^{\prime}$ while retaining the same designated scheme. For every test scheme $T$ over $R$ and points $x,y\in D(T)$, the underlying morphisms of the two canonical products agree: $$m_C(x,y)=m_{C^{\prime}}(x,y):T\longrightarrow D.$$ This equality preserves the integral family’s original group law when identifying its fibres with the literal field curves.
-- source:
--   Original complete transport_representation_relative_mul statement and proof body from MazurTheorem CurveIsoPicardPointMultiplicationTransport.lean, Apache-2.0, Vas and contributors. The original proof body is unchanged; the import changes to the public pointed-curve representation transport. Reuses original official Anthropic FLT Picard multiplication, universal-bundle and monoidal pullback APIs at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2. The complete original closed kernel type is compared with both the checked solution and public statement. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: Order13IntegralPicardLiteralFibreRelativeGroupCompatibility and the same family’s rational/mod-3/mod-5 arithmetic group identifications.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: transporting a Picard representation along a pointed curve
isomorphism preserves the canonical relative point multiplication on its
unchanged representing scheme. Named downstream consumer: relative group
compatibility of the actual integral family's arithmetic field fibres.
-/
import Mathlib
import Definitions.Def_MazurTransfer_PointedCurvePicardRepresentationTransport
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard GoodReductionJacobian NeronModelInfra
open MazurTransfer.CurveHomRigidifiedLineBundlePullback MazurTransfer.CurveIsoRigidifiedLineBundleTransport
open MazurTransfer.CurveIsoPicardRepresentationTransport
open scoped CategoryTheory.MonObj

theorem MazurTransfer.CurveIsoPicardPointMultiplicationTransport.transport_representation_relative_mul {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (.of R)} {c' : C' ⟶ Spec (.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (.of R))) c}
    {ε' : SchemeHomOver (𝟙 (Spec (.of R))) c'}
    (e : C' ≅ C) (he : e.hom ≫ c = c') (hε : ε'.val ≫ e.hom = ε.val)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    {T : Scheme.{u}} (t : T ⟶ Spec (.of R)) (x y : SchemeHomOver t D.toBase) :
    ((show RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition D from h).relativeGroupLaw.mul t x y).val =
    ((show RepresentsRelSubPic c' ε' (algEquivZeroGroupCut c' ε').toSubPicCondition
        (relabelDesignation (c' := c') D) from transportRepresentation e he hε D h).relativeGroupLaw.mul t x y).val := by sorry
