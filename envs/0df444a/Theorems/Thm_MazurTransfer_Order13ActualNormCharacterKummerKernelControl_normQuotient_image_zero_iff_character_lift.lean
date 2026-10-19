-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNormCharacterKummerKernelControl_normQuotient_image_zero_iff_character_lift
-- name    : MazurTransfer.Order13ActualNormCharacterKummerKernelControl.normQuotient_image_zero_iff_character_lift
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T02:51:28.121978+00:00
-- url     : https://prove2.me/theorems/4a16fa5f-be6e-49d2-832a-865cf05ee1f0
-- title:
--   Vanishing of an actual norm-character Kummer image is equivalent to a character H1 lift
-- statement:
--   Let \(K/\mathbb Q\) be the original characteristic-zero Galois field and \(\phi\) a finite endomorphism of the actual Picard group object with geometric kernel killed by \(19\). Suppose the norm homomorphism is geometrically surjective. Given intertwiners \(i:\sigma\to\ker\phi\) and \(p:\ker\phi\to\tau\) with \(i\) injective, \(p\) surjective and \(\operatorname{im}i=\ker p\), every rational norm-quotient class \(x\) satisfies \[\kappa_p(x)=1\quad\Longleftrightarrow\quad\exists y\in H^1_{\mathrm{cont}}(\operatorname{Aut}(K/\mathbb Q),\sigma),\ H^1(i)(y)=\kappa_\phi(x).\] Here \(\kappa_\phi\) is the original continuous norm Kummer class and \(\kappa_p\) its coefficient pushforward. The result controls the kernel of the character pushforward without asserting that it is injective. Named downstream consumer: the original exact norm-character Kummer sequence.
-- source:
--   Original MazurTheorem Order13ActualNormCharacterKummerKernelControl.normQuotient_image_zero_iff_character_lift, Apache-2.0. Complete original and public theorem types, thirteen original source instance types with eight nonproof values and four module values, and all thirteen statement providers are compared under unchanged default limits.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the kernel of an actual norm-character Kummer pushforward
is exactly the original norm Kummer classes lifted from the character-line
continuous H1. Named downstream consumer: actual norm Selmer kernel bounds.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormCharacterKummerKernelControlData
import Definitions.Def_MazurTransfer_Order13ActualNormCharacterH1GlobalExactnessBridgeData
import Definitions.Def_MazurTransfer_Order13ActualNormCharacterKummerPushforwardData

noncomputable section
open MazurTransfer
open MazurTransfer.Order13ActualNormCharacterKummerKernelControl
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages
open Order13ActualPicardNormKummerCocycles
open scoped CategoryTheory.MonObj
local instance publicNormCharacterKummerZeroCriterionStatementProvider120261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance publicNormCharacterKummerZeroCriterionStatementProvider220261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance publicNormCharacterKummerZeroCriterionStatementProvider320261018 : IsMonHom schemePi := schemePi_isMonHom
local instance publicNormCharacterKummerZeroCriterionStatementProvider420261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance publicNormCharacterKummerZeroCriterionStatementProvider520261018 : TopologicalSpace (Points K) := pointsTopology K
local instance publicNormCharacterKummerZeroCriterionStatementProvider620261018 : DiscreteTopology (Points K) := ⟨rfl⟩
local instance publicNormCharacterKummerZeroCriterionStatementProvider720261018 : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance publicNormCharacterKummerZeroCriterionStatementProvider820261018 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ



open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormContinuousCocycles
open Order13ActualPicardNormSubgroupRestriction Order13ActualPicardNormSubgroupRestrictionF19
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
local instance publicNormCharacterKummerZeroCriterionStatementProvider920261018 : Module (ZMod 19) (Additive (Kernel K φ)) := kernelZModModule K φ
local instance publicNormCharacterKummerZeroCriterionStatementProvider1020261018 : Module (ZMod 19) (ContinuousH1 K φ) := globalH1ZModModule K φ
local instance publicNormCharacterKummerZeroCriterionStatementProvider1120261018 : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) := kernel_continuousSMul K φ
open RepresentationDiscreteCoefficientInclusion
open Order13ActualNormCharacterContinuousH1
variable {U V : Type} [AddCommGroup U] [Module (ZMod 19) U]
  [AddCommGroup V] [Module (ZMod 19) V]
variable (σ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) U)
  (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
variable (i : Representation.IntertwiningMap σ (kernelRepresentation K φ))
  (p : Representation.IntertwiningMap (kernelRepresentation K φ) τ)
local instance publicNormCharacterKummerZeroCriterionStatementProvider1220261018 : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient σ)) :=
  coefficientH1ZModModule σ
local instance publicNormCharacterKummerZeroCriterionStatementProvider1320261018 : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient τ)) :=
  coefficientH1ZModModule τ

open Order13ActualNormCharacterH1Exactness Order13ActualNormCharacterKummerUnramified
open Order13ActualPicardNormContinuousKummerInjection
open Order13ActualPicardNormAlgebraicKummerInjection
variable (hsurj : Function.Surjective (normHom K φ))

theorem MazurTransfer.Order13ActualNormCharacterKummerKernelControl.normQuotient_image_zero_iff_character_lift
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap) (x : NormQuotient φ) :
    normQuotientCharacterHom K φ τ p hsurj x = 1 ↔
    ∃ y : ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient σ),
      inclusionClass K φ σ i y = (continuousQuotientHom K φ hsurj x).toAdd := by sorry
