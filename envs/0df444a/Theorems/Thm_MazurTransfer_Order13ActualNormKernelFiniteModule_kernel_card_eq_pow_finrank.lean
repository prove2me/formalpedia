-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNormKernelFiniteModule_kernel_card_eq_pow_finrank
-- name    : MazurTransfer.Order13ActualNormKernelFiniteModule.kernel_card_eq_pow_finrank
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T22:58:49.636795+00:00
-- url     : https://prove2.me/theorems/5ec01167-171e-460e-a7e0-b85fc7750b0b
-- title:
--   The original finite exponent-nineteen norm kernel has cardinality nineteen to its F19 rank
-- statement:
--   Let P be the same actual rational Picard group scheme, K a characteristic-zero field and phi a finite internal group endomorphism. Assume its field-valued kernel M is killed by nineteen and give it the original F19 module structure. Then $$|M|=19^{\dim_{\mathbf F_{19}}M}.$$ No value for that dimension, individual norm-kernel rank or isogeny degree is asserted. The named downstream consumers are the original nineteen-torsion dimension comparison and finite norm Selmer module bounds.
-- source:
--   Complete original MazurTheorem Order13ActualNormKernelFiniteModule.kernel_card_eq_pow_finrank statement and main proof. The original kernel, exponent hypothesis, finite-module structure and all relevant group/module provider values are retained and compared in full. Uses the original Mathlib finite-vector-space cardinality theorem. Official Anthropic FLT Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the actual geometric norm kernels are finite groups,
and their exponent nineteen makes them finite modules over F19.
Named downstream consumer: finite splitting fields and Galois module
structure needed for the actual norm Selmer bound.
-/
import Definitions.Def_MazurTransfer_Order13ActualNormKernelFiniteF19ModuleWithOriginalExponentFactsData20261017
noncomputable section
open MazurTransfer
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
open GoodReductionJacobian NeronModelInfra
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13ActualPicardDiamondSchemeEndomorphism
open Order13ActualPicardSchemeNineteenNorm Order13ActualPicardSchemeNormGroupHom
open Order13ActualPicardGeometricNormPreimages Order13ActualPicardNormKummerCocycles
open Order13ActualPicardNormKernelGaloisAction Order13ActualPicardGaloisFixedPointDescent
open scoped CategoryTheory.MonObj
local instance publicActualNormKernelCardStatementF19Provider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance publicActualNormKernelCardStatementF19Provider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj
open MazurTransfer.Order13ActualNormKernelFiniteModule
local instance publicActualNormKernelCardStatementFiniteProvider20261017 (K : Type) [Field K] [CharZero K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] :
    Finite (Kernel K φ) := kernel_finite K φ
local instance publicActualNormKernelCardStatementModuleProvider20261017 (K : Type) [Field K] [CharZero K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ]
    [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] : Module (ZMod 19) (Additive (Kernel K φ)) := kernelZModModule K φ
local instance publicActualNormKernelCardStatementPrimeProvider20261017 : Fact (Nat.Prime 19) := ⟨by decide⟩

theorem MazurTransfer.Order13ActualNormKernelFiniteModule.kernel_card_eq_pow_finrank (K : Type) [Field K] [CharZero K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left]
    [Fact (∀ z : Kernel K φ, z ^ 19 = 1)] :
    Nat.card (Kernel K φ) = 19 ^ Module.finrank (ZMod 19) (Additive (Kernel K φ)) := by sorry
