-- Prove2me | Theorems.Thm_MazurTransfer_order27_aggregate_products
-- name    : MazurTransfer.order27_aggregate_products
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T15:05:52.689868+00:00
-- url     : https://prove2.me/theorems/ab79f95c-638f-4b4e-afdd-10483d769076
-- title:
--   Order-27 third-leg aggregation: products
-- statement:
--   The displayed equalities hold for every rational family parameter and coordinate under their displayed kernel-cubic hypotheses. They are the complete original zlTD_val, zlTNSq_val, zlTNCb_val, zlTNSqTD_val, zlTNTD_val, zlTNTDSq_val, zlTDSq_val, zlTDCb_val identities, expressed using the fixed polynomial coefficient functions. The downstream consumer combines these products, coefficients, weighted terms and their vanishing sum to prove the original third-leg polynomial identity. No rational-point existence or torsion exclusion is assumed.
-- source:
--   User MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c. Full signatures extracted using Lean signature AST ranges; proof commands retained by kernel dependencies and resolved references. This is an exact split of the terminal timed-out third-leg polynomial verification, preserving the original hypotheses and conclusion. Original Apache-2.0 file headers retained.

import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData0
import Definitions.Def_MazurTransfer_OrderTwentySevenPolynomialData5

open MazurTorsion.Kubert

theorem MazurTransfer.order27_aggregate_products :
(∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
zlE0 f Z * zlE0 f Z =
      (zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) ∧
(∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) * ((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z +
      zlTN3 Z)) =
      (((zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) + (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z)) +
        ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z + zlTNSqP1c3 f Z))) +
        (((zlTNSqP1c4 f Z + zlTNSqP2c0 f Z) + (zlTNSqP2c1 f Z + zlTNSqP2c2 f Z)) +
        (zlTNSqP2c3 f Z + zlTNSqP2c4 f Z))) ∧
(∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) * ((((zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) +
      (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z)) + ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z +
      zlTNSqP1c3 f Z))) + (((zlTNSqP1c4 f Z + zlTNSqP2c0 f Z) + (zlTNSqP2c1 f Z + zlTNSqP2c2 f Z))
      + (zlTNSqP2c3 f Z + zlTNSqP2c4 f Z))) =
      (zlTNCbP0c0 f + zlTNCbP0c1 f) + zlTNCbP0c2 f) ∧
(∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) * ((((zlTNSqP0c0 f Z + zlTNSqP0c1 f Z) +
      (zlTNSqP0c2 f Z + zlTNSqP0c3 f Z)) + ((zlTNSqP1c0 f Z + zlTNSqP1c1 f Z) + (zlTNSqP1c2 f Z +
      zlTNSqP1c3 f Z))) + (((zlTNSqP1c4 f Z + zlTNSqP2c0 f Z) + (zlTNSqP2c1 f Z + zlTNSqP2c2 f Z))
      + (zlTNSqP2c3 f Z + zlTNSqP2c4 f Z))) =
      ((zlTNSqTDP0c0 f Z + zlTNSqTDP0c1 f Z) + (zlTNSqTDP0c2 f Z + zlTNSqTDP0c3 f Z)) +
        ((zlTNSqTDP0c4 f Z + zlTNSqTDP0c5 f Z) + (zlTNSqTDP0c6 f Z + zlTNSqTDP0c7 f Z))) ∧
(∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
((zlTN0 f Z + zlTN1 f Z) + (zlTN2 f Z + zlTN3 Z)) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2
      f Z) =
      (((zlTNTDP0c0 f Z + zlTNTDP0c1 f Z) + (zlTNTDP0c2 f Z + zlTNTDP0c3 f Z)) +
        ((zlTNTDP0c4 f Z + zlTNTDP1c0 f Z) + (zlTNTDP1c1 f Z + zlTNTDP1c2 f Z))) +
        (zlTNTDP1c3 f Z + zlTNTDP1c4 f Z)) ∧
(∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
((((zlTNTDP0c0 f Z + zlTNTDP0c1 f Z) + (zlTNTDP0c2 f Z + zlTNTDP0c3 f Z)) + ((zlTNTDP0c4 f Z +
      zlTNTDP1c0 f Z) + (zlTNTDP1c1 f Z + zlTNTDP1c2 f Z))) + (zlTNTDP1c3 f Z + zlTNTDP1c4 f Z)) *
      ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      ((((zlTNTDSqP0c0 f Z + zlTNTDSqP0c1 f Z) + (zlTNTDSqP0c2 f Z + zlTNTDSqP0c3 f Z)) +
        ((zlTNTDSqP0c4 f Z + zlTNTDSqP1c0 f Z) + (zlTNTDSqP1c1 f Z + zlTNTDSqP1c2 f Z))) +
        (((zlTNTDSqP1c3 f Z + zlTNTDSqP1c4 f Z) + (zlTNTDSqP1c5 f Z + zlTNTDSqP2c0 f Z)) +
        ((zlTNTDSqP2c1 f Z + zlTNTDSqP2c2 f Z) + (zlTNTDSqP2c3 f Z + zlTNTDSqP2c4 f Z))))
        + (((zlTNTDSqP3c0 f Z + zlTNTDSqP3c1 f Z) + (zlTNTDSqP3c2 f Z + zlTNTDSqP3c3 f Z))
        + (zlTNTDSqP3c4 f Z + zlTNTDSqP3c5 f Z))) ∧
(∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) * ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f
      Z) =
      ((zlTDSqP0c0 f Z + zlTDSqP0c1 f Z) + (zlTDSqP0c2 f Z + zlTDSqP0c3 f Z)) + zlTDSqP0c4
        f Z) ∧
(∀ {f Z : ℚ} (hM : kernelCubicM f Z = 0),
(((zlTDSqP0c0 f Z + zlTDSqP0c1 f Z) + (zlTDSqP0c2 f Z + zlTDSqP0c3 f Z)) + zlTDSqP0c4 f Z) *
      ((zlTDP0c0 f Z + zlTDP0c1 f Z) + zlTDP0c2 f Z) =
      (((zlTDCbP0c0 f Z + zlTDCbP0c1 f Z) + (zlTDCbP0c2 f Z + zlTDCbP0c3 f Z)) +
        ((zlTDCbP0c4 f Z + zlTDCbP1c0 f Z) + (zlTDCbP1c1 f Z + zlTDCbP1c2 f Z))) +
        ((zlTDCbP1c3 f Z + zlTDCbP1c4 f Z) + zlTDCbP1c5 f Z)) := by sorry
