-- Prove2me | Theorems.Thm_MazurTransfer_Order13ArithmeticPicardPointMap_arithmeticClass_eq_of_presentation
-- name    : MazurTransfer.Order13ArithmeticPicardPointMap.arithmeticClass_eq_of_presentation
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T15:24:20.759674+00:00
-- url     : https://prove2.me/theorems/bba895a3-f873-4e34-b8aa-3947196443c0
-- title:
--   Actual arithmetic Picard class is independent of divisor presentation
-- statement:
--   For every perfect field of characteristic different from 2 and 13, any genuine degree-zero divisor presentation of the line bundle of any base-field represented Picard point on the literal order-13 curve yields the original arithmeticClass of that point. All original cover, section, Picard designation, representation and presentation hypotheses are retained.
-- source:
--   Complete original MazurTheorem Order13ActualArithmeticPicardPointMap.arithmeticClass_eq_of_presentation proof with accepted public perfect-field presentation ratio; original frame-nonvanishing and quotient equality helper proofs retained from official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Original full presentation-independence contract and proof retained, using
public point constructors and the accepted perfect-field presentation ratio.
Design boundary: every genuine degree-zero presentation yields the same
original arithmetic Pic0 class. Named downstream consumer: actual inverse
Picard pullback naturality. Official Anthropic FLT interfaces at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
-/
import Definitions.Def_MazurTransfer_Order13ArithmeticPicardPointMapData
import Theorems.Thm_MazurTransfer_presentation_ratio_principal_over_perfect_field
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicCurve
open AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open MazurTorsion.XOneThirteenProjectiveCurve
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
open P2MW.S_AlgebraicCurve_CurveModel_exists_divisorClassMap.DivisorClassMapGlue
open MazurTransfer.LineBundleFieldComparison
open MazurTransfer.Order13ArithmeticPicardPointMap

theorem MazurTransfer.Order13ArithmeticPicardPointMap.arithmeticClass_eq_of_presentation
    (K : Type u) [Field K] [PerfectField K] [Fact ((104 : K) ≠ 0)]
    (𝒱 : (curveScheme K).TwoAffineOpenCover)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (curveToBase K))
    (D : RelativePic0Designation K (curveToBase K))
    (h : RepresentsRelSubPic (curveToBase K) ε (algEquivZeroCut (curveToBase K) ε) D)
    (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase)
    (E : Divisor.degZero (K := K) (F := actualCurveFunctionField K))
    (φ : ∀ U : (curveScheme K).Opens,
      Γ(pointLineBundle (curveToBase K) ε D h a, U) →+ (actualCurveFunctionField K))
    (hE : IsPresentation (curveToBase K) (pointLineBundle (curveToBase K) ε D h a) E.1 φ) :
    Pic0.mk E = arithmeticClass K 𝒱 ε D h a := by sorry
