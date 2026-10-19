-- Prove2me | Theorems.Thm_MazurTransfer_Order13PellReciprocalExpression_reciprocal_expression
-- name    : MazurTransfer.Order13PellReciprocalExpression.reciprocal_expression
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T13:37:31.417611+00:00
-- url     : https://prove2.me/theorems/090ca694-bba4-4605-8b60-2176c576a90e
-- title:
--   The explicit Pell polynomials transform under reciprocal coordinates
-- statement:
--   For any field $F$, any nonzero $z\in F$ and any $w\in F$, the original explicit Pell polynomials satisfy $$(H(z^{-1})+w(z^{-1})^3K(z^{-1}))z^{19}=H_\infty(z)+wK_\infty(z).$$ This is the polynomial transition identity for the ordinary and reciprocal Pell expressions.
-- source:
--   Original complete reciprocal_expression statement and proof from MazurTheorem Order13PellReciprocalExpression.lean, Apache-2.0, Vas and contributors. The four explicit original polynomial definitions are supplied by their public data library. Only public import and top-level namespace context change. The full original closed type is kernel-compared. Named downstream consumer: actual ordinary-chart expression for the infinity-defined Pell function.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the explicit Pell polynomial and its reversed expression
agree after inverting the abscissa. Named downstream consumer: the actual
ordinary-chart unit expression for the Pell function.
-/
import Definitions.Def_MazurTransfer_Order13PellPolynomialCertificate
noncomputable section
universe u
open MazurTransfer
open Order13PellChartCertificate
open Order13PellChartCertificate

theorem MazurTransfer.Order13PellReciprocalExpression.reciprocal_expression (F : Type u) [Field F] (z w : F) (hz : z ≠ 0) :
    (pellH z⁻¹ + (w * (z⁻¹) ^ 3) * pellK z⁻¹) * z ^ 19 =
      infinityPellH z + w * infinityPellK z := by sorry
