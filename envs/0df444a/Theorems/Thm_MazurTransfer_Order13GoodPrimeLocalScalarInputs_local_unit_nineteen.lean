-- Prove2me | Theorems.Thm_MazurTransfer_Order13GoodPrimeLocalScalarInputs_local_unit_nineteen
-- name    : MazurTransfer.Order13GoodPrimeLocalScalarInputs.local_unit_nineteen
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T03:31:34.419914+00:00
-- url     : https://prove2.me/theorems/e80265b4-45b1-46a1-9f6a-1dab0fdb9e91
-- title:
--   Nineteen is a unit in the original local integer coefficient ring away from nineteen
-- statement:
--   Let $q$ be a prime different from $19$. In the original local integer coefficient ring,
--
--   $$
--   19\in\mathbb Z_{(q)}^\times.
--   $$
--
--   This is the scalar input for finite flat and étale multiplication by nineteen, and then for the same integral norm factors at good primes. The complete original prime telescope is retained.
-- source:
--   Original MazurTheorem Order13GoodPrimeLocalScalarInputs.local_unit_nineteen, Apache-2.0. Complete original and public types and standalone complete telescope are compared under default options.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the SAME selected local Picard law is commutative and
nineteen is invertible in the actual coefficient ring at other primes.
Named downstream consumer: finite flat etale local scalar nineteen and
the SAME integral norm factors.
-/
import Definitions.Def_MazurTransfer_Order13LocalIntegralCoefficientMaps

noncomputable section
open MazurTransfer.Order13LocalIntegralCoefficientMaps

theorem MazurTransfer.Order13GoodPrimeLocalScalarInputs.local_unit_nineteen (q : ℕ) [Fact q.Prime] (hne : q ≠ 19) : IsUnit (19 : LocalRing q) := by sorry
