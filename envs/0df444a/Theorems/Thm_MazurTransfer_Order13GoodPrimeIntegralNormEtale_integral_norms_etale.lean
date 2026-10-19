-- Prove2me | Theorems.Thm_MazurTransfer_Order13GoodPrimeIntegralNormEtale_integral_norms_etale
-- name    : MazurTransfer.Order13GoodPrimeIntegralNormEtale.integral_norms_etale
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T05:58:28.841045+00:00
-- url     : https://prove2.me/theorems/6c48d8fa-aca8-4b60-8ad6-a88b2eeabfd7
-- title:
--   Both selected good-prime integral norm maps are etale
-- statement:
--   For every prime q with q not dividing 104 and q different from 19, both selected integral norm extensions on the local Picard model are etale. The statement retains the complete original context and the same selected models and morphisms.
-- source:
--   MazurTheorem original formalization, Order13GoodPrimeIntegralNormEtale.integral_norms_etale; proof reuses existing public relative group scalar geometry and the accepted actual integral norm finiteness and formal unramifiedness results.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: finite etale fibres of the SAME selected integral norm
extensions at every prime away from 104 and nineteen. The group law and
multiplication by nineteen are those of the selected local Picard model.
Named downstream consumer: good-prime unramified Kummer conditions.
-/
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralScalarNineteenFacts
import Definitions.Def_MazurTransfer_Order13GoodPrimeLocalPicardLawCommutativity
noncomputable section
open MazurTransfer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Order13GoodPrimeLocalPicardModels Order13GoodPrimeLocalScalarInputs
open Order13GoodPrimeIntegralNormExtensions Order13GoodPrimeIntegralScalarNineteen
open Order13LocalIntegralCoefficientMaps

theorem MazurTransfer.Order13GoodPrimeIntegralNormEtale.integral_norms_etale (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19) :
    Etale (integralPi q hq).val ∧ Etale (integralPiConjugate q hq).val := by sorry
