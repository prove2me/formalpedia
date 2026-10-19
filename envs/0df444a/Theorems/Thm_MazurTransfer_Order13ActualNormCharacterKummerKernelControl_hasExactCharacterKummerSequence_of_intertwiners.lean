-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNormCharacterKummerKernelControl_hasExactCharacterKummerSequence_of_intertwiners
-- name    : MazurTransfer.Order13ActualNormCharacterKummerKernelControl.hasExactCharacterKummerSequence_of_intertwiners
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T03:03:42.415594+00:00
-- url     : https://prove2.me/theorems/05f67b2b-0038-4b7f-8d1d-91bbbe0b784b
-- title:
--   Exact actual norm-character intertwiners give the original exact Kummer sequence
-- statement:
--   For the same actual Picard norm kernel over the original characteristic-zero Galois field \(K/\mathbb Q\), retain the finite-endomorphism, exponent-nineteen and geometric norm-surjectivity hypotheses. Given intertwiners \(i:\sigma\to\ker\phi\) and \(p:\ker\phi\to\tau\) with \(i\) injective, \(p\) surjective and \(\operatorname{im}i=\ker p\), the original predicate \(\operatorname{HasExactCharacterKummerSequence}\) holds. It combines the specified representation exactness, middle continuous H1 exactness and the kernel formula \[\kappa_p(x)=1\ \Longleftrightarrow\ \exists y,\ H^1(i)(y)=\kappa_\phi(x).\] Arithmetic intertwiners and geometric norm surjectivity remain inputs. Named downstream consumer: actual norm-character Selmer kernel bounds.
-- source:
--   Original MazurTheorem Order13ActualNormCharacterKummerKernelControl.hasExactCharacterKummerSequence_of_intertwiners, Apache-2.0. Complete original and public final types, all thirteen original source providers with eight nonproof values and four module values, and all thirteen statement providers are compared.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the kernel of an actual norm-character Kummer pushforward
is exactly the original norm Kummer classes lifted from the character-line
continuous H1. Named downstream consumer: actual norm Selmer kernel bounds.
-/
import Theorems.Thm_MazurTransfer_Order13ActualNormCharacterKummerKernelControl_normQuotient_image_zero_iff_character_lift
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
local instance publicNormCharacterKummerExactSequenceStatementProvider120261018 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance publicNormCharacterKummerExactSequenceStatementProvider220261018 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
local instance publicNormCharacterKummerExactSequenceStatementProvider320261018 : IsMonHom schemePi := schemePi_isMonHom
local instance publicNormCharacterKummerExactSequenceStatementProvider420261018 : IsMonHom schemePiConjugate := schemePiConjugate_isMonHom

open Order13ActualPicardNormKernelGaloisAction
open Order13ActualPicardGaloisFixedPointDescent
variable (K : Type) [Field K] [CharZero K] [IsGalois ℚ K]
variable (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
local instance publicNormCharacterKummerExactSequenceStatementProvider520261018 : TopologicalSpace (Points K) := pointsTopology K
local instance publicNormCharacterKummerExactSequenceStatementProvider620261018 : DiscreteTopology (Points K) := ⟨rfl⟩
local instance publicNormCharacterKummerExactSequenceStatementProvider720261018 : MulAction (K ≃ₐ[ℚ] K) (Points K) :=
  { smul := MazurTransfer.FieldAutomorphismOverPointAction.act actualPicard.toBase
    one_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_one actualPicard.toBase
    mul_smul := MazurTransfer.FieldAutomorphismOverPointAction.act_mul actualPicard.toBase }
local instance publicNormCharacterKummerExactSequenceStatementProvider820261018 : MulDistribMulAction (K ≃ₐ[ℚ] K) (Kernel K φ) := kernelAction K φ



open Order13ActualNormKernelF19Representation Order13ActualNormKernelFiniteModule
open Order13ActualPicardNormContinuousCohomology Order13ActualPicardNormContinuousCocycles
open Order13ActualPicardNormSubgroupRestriction Order13ActualPicardNormSubgroupRestrictionF19
open RepresentationDiscreteCoefficients ContinuousCoefficientExponentAndContinuity
variable [IsFinite φ.left] [Fact (∀ z : Kernel K φ, z ^ 19 = 1)]
local instance publicNormCharacterKummerExactSequenceStatementProvider920261018 : Module (ZMod 19) (Additive (Kernel K φ)) := kernelZModModule K φ
local instance publicNormCharacterKummerExactSequenceStatementProvider1020261018 : Module (ZMod 19) (ContinuousH1 K φ) := globalH1ZModModule K φ
local instance publicNormCharacterKummerExactSequenceStatementProvider1120261018 : ContinuousSMul (K ≃ₐ[ℚ] K) (Kernel K φ) := kernel_continuousSMul K φ
open RepresentationDiscreteCoefficientInclusion
open Order13ActualNormCharacterContinuousH1
variable {U V : Type} [AddCommGroup U] [Module (ZMod 19) U]
  [AddCommGroup V] [Module (ZMod 19) V]
variable (σ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) U)
  (τ : Representation (ZMod 19) (K ≃ₐ[ℚ] K) V)
variable (i : Representation.IntertwiningMap σ (kernelRepresentation K φ))
  (p : Representation.IntertwiningMap (kernelRepresentation K φ) τ)
local instance publicNormCharacterKummerExactSequenceStatementProvider1220261018 : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient σ)) :=
  coefficientH1ZModModule σ
local instance publicNormCharacterKummerExactSequenceStatementProvider1320261018 : Module (ZMod 19)
    (ContinuousFirstCohomologyPresentation.H1 (K ≃ₐ[ℚ] K) (Coefficient τ)) :=
  coefficientH1ZModModule τ

open Order13ActualNormCharacterH1Exactness Order13ActualNormCharacterKummerUnramified
open Order13ActualPicardNormContinuousKummerInjection
open Order13ActualPicardNormAlgebraicKummerInjection
variable (hsurj : Function.Surjective (normHom K φ))

theorem MazurTransfer.Order13ActualNormCharacterKummerKernelControl.hasExactCharacterKummerSequence_of_intertwiners
    (hi : Function.Injective i) (hp : Function.Surjective p)
    (hk : LinearMap.range i.toLinearMap = LinearMap.ker p.toLinearMap) :
    HasExactCharacterKummerSequence K φ σ τ hsurj := by sorry
