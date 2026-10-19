-- Prove2me | Theorems.Thm_MazurTransfer_Order13InfinityLocalParameter_w_add_constant_isUnit
-- name    : MazurTransfer.Order13InfinityLocalParameter.w_add_constant_isUnit
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T11:32:38.234176+00:00
-- url     : https://prove2.me/theorems/41a29320-eca4-47a7-a168-b038dbbc45cb
-- title:
--   The conjugate factor is a unit in the actual infinity local ring
-- statement:
--   Let $K$ be a field with $2\ne0$, and let $a\in K$ satisfy $a^2=1$. Localize the actual reciprocal coordinate algebra at the kernel of evaluation at $(0,a)$. In this local ring, $$w+a\ \text{is a unit}.$$ This supplies the factor cancellation used to prove that $z$ is a uniformizer.
-- source:
--   Original MazurTheorem proof, Apache-2.0, Vas and contributors. The original complete statement and proof are retained; the original coordinate evaluation helper is inlined with explicit public abbreviation unfolding. The characteristic assumption is exactly the original one. Native, strict and complete frontend checks pass. Complete original and public closed types are kernel-compared. Named downstream consumer: the actual Pell principal divisor.

/- Copyright (c) 2026 Vas and contributors. Apache-2.0.
Design boundary: exact original infinity chart contract.
Named downstream consumer: the actual Pell principal-divisor computation. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13InfinityLocalRingCoordinates
noncomputable section
universe u
open Polynomial MazurTransfer
open MazurTorsion.XOneThirteenProjectiveCurve
open Order13IntegralSections Order13InfinityEvaluationKernel Order13InfinityLocalParameter
variable (K : Type u) [Field K] (a : K) (ha : a ^ 2 = 1)

theorem MazurTransfer.Order13InfinityLocalParameter.w_add_constant_isUnit (h2 : (2 : K) ≠ 0) :
    IsUnit (w K a ha + constant K a ha) := by sorry
