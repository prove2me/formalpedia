-- Prove2me | Theorems.Thm_MazurTransfer_Order13OrdinaryChartComplement_point_in_ordinary_or_infinity
-- name    : MazurTransfer.Order13OrdinaryChartComplement.point_in_ordinary_or_infinity
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T13:41:30.166402+00:00
-- url     : https://prove2.me/theorems/e9964743-7403-4b5f-a14f-0c344015ea84
-- title:
--   Every point of the actual order-13 curve is ordinary or one of the two infinity centers
-- statement:
--   Every point $x$ of the literal order-13 curve over $\mathbb Q$ lies in its ordinary affine chart or equals the positive or negative reciprocal infinity center. Equivalently, the complement of the ordinary chart consists exactly of the two specified infinity points. This determines the possible support of the explicit Pell principal divisor.
-- source:
--   Original complete point_in_ordinary_or_infinity statement and proof from MazurTheorem Order13OrdinaryChartComplement.lean, Apache-2.0, Vas and contributors. Its two original coordinate/prime-ideal helpers are retained in an explicit fresh namespace. Public original infinity, polynomial and chart-range interfaces supply all dependencies. The full original closed type is kernel-compared. Named downstream consumer: Pell orders vanish at every place away from the two actual infinity sections.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the complement of the ordinary affine chart consists of
the two literal infinity section points. Named downstream consumer: the
complete support calculation for the Pell principal divisor.
-/
import Definitions.Def_MazurTransfer_Order13ActualInfinityPlaceCenterData
import Definitions.Def_MazurTransfer_Order13PellPolynomialCertificate
import Definitions.Def_MazurTransfer_Order13PellInfinityLocalOrders
import Theorems.Thm_MazurTransfer_Order13IntegralHyperellipticMap_reciprocalChartMap_preimage_ordinaryChartMap_opensRange_eq_basicOpen
import Theorems.Thm_MazurTransfer_Order13InfinityEvaluationKernel_evaluation_kernel
noncomputable section
open MazurTransfer

open AlgebraicGeometry CategoryTheory Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13InfinityLocalParameter MazurTransfer.Order13InfinityEvaluationKernel
open MazurTransfer.Order13ActualInfinityPlaceCenters
local instance : Fact ((104 : ℚ) ≠ 0) := ⟨by norm_num⟩

theorem MazurTransfer.Order13OrdinaryChartComplement.point_in_ordinary_or_infinity (x : curveScheme ℚ) :
    x ∈ (ordinaryChartMap ℚ).opensRange ∨
      x = center 1 (Order13PellInfinityLocalOrders.positiveProof ℚ) ∨
      x = center (-1) (Order13PellInfinityLocalOrders.negativeProof ℚ) := by sorry
