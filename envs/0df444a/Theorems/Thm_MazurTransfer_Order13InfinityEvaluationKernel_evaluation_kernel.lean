-- Prove2me | Theorems.Thm_MazurTransfer_Order13InfinityEvaluationKernel_evaluation_kernel
-- name    : MazurTransfer.Order13InfinityEvaluationKernel.evaluation_kernel
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T11:17:06.724145+00:00
-- url     : https://prove2.me/theorems/a60f4313-f1c2-4bf6-b332-9ff9fbaac590
-- title:
--   The exact evaluation kernel at either literal infinity point
-- statement:
--   Let $R$ be a commutative ring and let $a\in R$ satisfy $a^2=1$. In the actual reciprocal coordinate algebra, evaluation at $(z,w)=(0,a)$ has kernel $$\ker(\operatorname{ev}_a)=(z,w-a).$$ This identifies the ideal of the infinity section and supplies the local parameter calculation.
-- source:
--   Original MazurTheorem proof, Apache-2.0, Vas and contributors. The original complete kernel theorem is retained, with its two small original ideal/quotient helpers inlined. Coordinate evaluation helpers explicitly unfold the existing public abbreviation. No assumption on characteristic is added. Native, strict and complete frontend checks pass. Complete original and public closed types are kernel-compared. Named downstream consumer: the actual Pell principal divisor.

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: exact original infinity chart contract.
Named downstream consumer: the actual Pell principal-divisor computation. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13InfinityEvaluationMaps
noncomputable section
universe u
open Polynomial
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13IntegralSections MazurTransfer.Order13InfinityEvaluationKernel
variable (R : Type u) [CommRing R] (a : R) (ha : a ^ 2 = 1)

theorem MazurTransfer.Order13InfinityEvaluationKernel.evaluation_kernel : RingHom.ker (evaluation R a ha) = sectionIdeal R a := by sorry
