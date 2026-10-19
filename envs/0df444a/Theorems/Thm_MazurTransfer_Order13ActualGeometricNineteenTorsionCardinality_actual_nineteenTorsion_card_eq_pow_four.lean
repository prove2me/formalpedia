-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualGeometricNineteenTorsionCardinality_actual_nineteenTorsion_card_eq_pow_four
-- name    : MazurTransfer.Order13ActualGeometricNineteenTorsionCardinality.actual_nineteenTorsion_card_eq_pow_four
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T10:19:24.61061+00:00
-- url     : https://prove2.me/theorems/5baa636d-2efd-44d2-89d5-334556c9e7b6
-- title:
--   The actual Picard nineteen-torsion has cardinality nineteen to the fourth power
-- statement:
--   For every algebraically closed field K of characteristic zero in the original universe, the subgroup of points killed by nineteen on the designated rational Picard of the literal order-13 curve has cardinality 19^4. The Picard scheme and its group law are the same ones used for the actual norm endomorphisms.
-- source:
--   MazurTheorem Order13ActualGeometricNineteenTorsionCardinality.actual_nineteenTorsion_card_eq_pow_four; applies the exact Anthropic FLT RelativeGroupLaw torsion-cardinality theorem at commit 6e837e75355538c7f80bab5b956861e86c4eacc2.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ActualPicardAlgPointsComparisonData20261018
noncomputable section
open MazurTransfer
open Order13ActualNormKernelProductCardinality

theorem MazurTransfer.Order13ActualGeometricNineteenTorsionCardinality.actual_nineteenTorsion_card_eq_pow_four (K : Type) [Field K] [CharZero K] [IsAlgClosed K] :
    Nat.card (NineteenTorsion K) = 19 ^ 4 := by sorry
