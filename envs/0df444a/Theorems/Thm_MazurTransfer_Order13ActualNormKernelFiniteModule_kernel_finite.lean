-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualNormKernelFiniteModule_kernel_finite
-- name    : MazurTransfer.Order13ActualNormKernelFiniteModule.kernel_finite
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T22:42:27.396796+00:00
-- url     : https://prove2.me/theorems/6983aa9e-d276-42b3-8dfe-1f07abd77844
-- title:
--   A finite endomorphism of the actual Picard has finite kernels on all characteristic-zero field points
-- statement:
--   Let P be the same actual rational represented Picard group scheme, K any characteristic-zero field, and phi an internal monoid endomorphism whose underlying scheme morphism is finite. Then $$\ker\bigl(\varphi:P(K)\to P(K)\bigr)\ \text{is finite}.$$ The kernel is the original subgroup of the original point homomorphism. No Galois, algebraic-closure or étaleness assumption is added. The named downstream consumers are finite F19 norm-kernel modules, splitting fields and norm Selmer conditions.
-- source:
--   Complete original MazurTheorem Order13ActualNormKernelFiniteModule.kernel_finite statement and main proof. Same actual represented Picard, original kernel/point/scalar-extension constructors, and full original group providers. The proof-only continuity import is removed, while the original literal-fibre encoding is retained. Complete original final type and all relevant group/action providers and dependency providers are compared. Official Anthropic FLT Picard interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

import Definitions.Def_MazurTransfer_Order13ActualPicardNormKernelGaloisActionData
import Definitions.Def_MazurTransfer_Order13ActualPicardRationalFixedPointGroupData
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
local instance publicActualNormKernelFiniteStatementProvider120261017 : GrpObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).grpObj
local instance publicActualNormKernelFiniteStatementProvider220261017 : IsCommMonObj (Over.mk actualPicard.toBase) :=
  (show RepresentsRelSubPic (curveToBase ℚ) infinitySection
    (algEquivZeroGroupCut (curveToBase ℚ) infinitySection).toSubPicCondition actualPicard
    from actualRepresentation).isCommMonObj

theorem MazurTransfer.Order13ActualNormKernelFiniteModule.kernel_finite (K : Type) [Field K] [CharZero K]
    (φ : Over.mk actualPicard.toBase ⟶ Over.mk actualPicard.toBase) [IsMonHom φ] [IsFinite φ.left] : Finite (Kernel K φ) := by sorry
