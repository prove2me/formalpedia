-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualIntegralPicardFamilyBaseChanges_actual_integral_picard_family_baseChanges
-- name    : MazurTransfer.Order13ActualIntegralPicardFamilyBaseChanges.actual_integral_picard_family_baseChanges
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T07:34:20.154111+00:00
-- url     : https://prove2.me/theorems/df444464-8a48-4f92-b652-418c95d5af64
-- title:
--   One actual integral order-thirteen Picard family under every algebra base change
-- statement:
--   Let $R$ be a noetherian commutative integral domain in which $104$ is invertible, and let $C/R$ be the literal order-thirteen curve with positive-infinity section $\varepsilon$. There exists one designated scheme $D$ representing the algebraically trivial rigidified relative Picard subfunctor, with smooth, proper and geometrically connected structure morphism. For every commutative $R$-algebra $A$, the designated base change $D_A$ represents the corresponding subfunctor of $C_A$ and $\varepsilon_A$, and $$D_A\longrightarrow\operatorname{Spec}A\quad\text{is smooth, proper and geometrically connected}.$$ The same family $D$ works simultaneously for every algebra base change. This supplies the common family for rational and good-characteristic fibres.
-- source:
--   Original complete actual_integral_picard_family_baseChanges contract and proof body from MazurTheorem Order13ActualIntegralPicardFamilyBaseChanges.lean, Apache-2.0, Vas and contributors. Reuses the publicly Proved actual integral Picard representation and the original official Anthropic FLT base-change theorem, exact upstream pin 6e837e75355538c7f80bab5b956861e86c4eacc2. The complete 19796-character original closed kernel type is independently exported and compared against the solution and public statement, including universe parameters and all actual structural maps. The original single witness is retained under every base change; no equality with independently chosen field Picard schemes is assumed. Named downstream consumers: the same integral Picard family over the rational, mod-3 and mod-5 fields and literal fibre arithmetic identifications.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: one actual integral Picard representing scheme has
compatible original Picard representations after every algebra base change;
its smoothness, properness and geometric connectedness persist.
Named downstream consumer: rational/mod-3/mod-5 fibres of this same family.
No identification with independently selected field Picards is assumed.
-/
import Mathlib
import Theorems.Thm_MazurTransfer_Order13ActualIntegralPicardRepresentation_actual_integral_picard_representation
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_baseChange
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicGeometry.SmoothProperCurve GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer

theorem MazurTransfer.Order13ActualIntegralPicardFamilyBaseChanges.actual_integral_picard_family_baseChanges (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] (h104 : IsUnit (104 : R)) :
    ∃ D : RelativePic0Designation R (curveToBase R),
      Nonempty (RepresentsRelSubPic (curveToBase R)
        (Order13IntegralSections.positiveInfinitySection R)
        (algEquivZeroCut (curveToBase R) (Order13IntegralSections.positiveInfinitySection R)) D) ∧
      Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Nonempty (RepresentsRelSubPic (baseChange R (curveToBase R) A)
          (sectionBaseChange A (Order13IntegralSections.positiveInfinitySection R))
          (algEquivZeroCut (baseChange R (curveToBase R) A)
            (sectionBaseChange A (Order13IntegralSections.positiveInfinitySection R)))
          (D.baseChange A)) ∧
        Smooth (D.baseChange A).toBase ∧ IsProper (D.baseChange A).toBase ∧
        GeometricallyConnected (D.baseChange A).toBase := by sorry
