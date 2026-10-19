-- Prove2me | Theorems.Thm_MazurTransfer_Order13GoodPrimeIntegralNormEtale_integral_norm_fibres_finite_etale
-- name    : MazurTransfer.Order13GoodPrimeIntegralNormEtale.integral_norm_fibres_finite_etale
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-18T06:10:29.096156+00:00
-- url     : https://prove2.me/theorems/d740ed9d-da2d-45d9-911e-ffa81105d032
-- title:
--   Arbitrary fibres of both selected good-prime integral norm maps are finite etale
-- statement:
--   For every prime q not dividing 104 and different from 19, the fibres of both selected integral norm maps over every scheme T and every T-valued local Picard point are finite etale. The complete original telescope is retained.
-- source:
--   MazurTheorem original Order13GoodPrimeIntegralNormEtale.integral_norm_fibres_finite_etale.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: finite etale fibres of the SAME selected integral norm
extensions at every prime away from 104 and nineteen. The group law and
multiplication by nineteen are those of the selected local Picard model.
Named downstream consumer: good-prime unramified Kummer conditions.
-/
import Definitions.Def_MazurTransfer_Order13GoodPrimeIntegralScalarNineteenFacts
noncomputable section
open MazurTransfer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open Order13GoodPrimeLocalPicardModels
open Order13GoodPrimeIntegralNormExtensions Order13GoodPrimeIntegralScalarNineteen
open Order13LocalIntegralCoefficientMaps

theorem MazurTransfer.Order13GoodPrimeIntegralNormEtale.integral_norm_fibres_finite_etale (q : ℕ) [Fact q.Prime] (hq : ¬ (q : ℤ) ∣ 104) (hne : q ≠ 19) {T : Scheme}
    (x : T ⟶ (localPicard q hq).P) :
    (IsFinite (pullback.snd (integralPi q hq).val x) ∧
      Etale (pullback.snd (integralPi q hq).val x)) ∧
    (IsFinite (pullback.snd (integralPiConjugate q hq).val x) ∧
      Etale (pullback.snd (integralPiConjugate q hq).val x)) := by sorry
