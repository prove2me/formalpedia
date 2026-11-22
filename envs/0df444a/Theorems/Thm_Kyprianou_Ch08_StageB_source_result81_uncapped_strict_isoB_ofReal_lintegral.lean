-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_source_result81_uncapped_strict_isoB_ofReal_lintegral
-- name    : Kyprianou.Ch08.StageB.source_result81_uncapped_strict_isoB_ofReal_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T03:29:32.545752+00:00
-- url     : https://prove2.me/theorems/80f829b2-f58b-4ab5-9d2d-9c2a4b16250d
-- title:
--   Uncapped stopped ofReal integral to lintegral conversion
-- statement:
--   Given integrability and nonnegativity of the stopped weight, payoff, and ordinary reward, their ofReal integrals equal the corresponding ENNReal lintegrals with ofReal lifts. This is a technical extraction of the parent uncapped proof, isolating real-to-ENNReal conversion and pointwise ofReal reconciliation without the strong-Markov factorization itself.
-- source:
--   Strict-isolation extraction of parent 16d2c69d-3c6f-4486-8687-1d77d4d48ea0 bridge (complexity 0.4471). Helper ISO-B isolates ofReal-to-lintegral conversion and pointwise ENNReal equalities; factorization itself remains in parent via H2. No sibling H1/H2 proof dependency.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ENNReal.Operations
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch08.StageB.source_result81_uncapped_strict_isoB_ofReal_lintegral
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P F) (lower upper : ℝ)
    (discount : ℝ≥0 → ℝ) (hd : Measurable discount) (hdb : ∀ t, 0 ≤ discount t ∧ discount t ≤ 1)
    (reward : (ℝ≥0 → ℝ) → ℝ) (hr : Measurable reward) (hrb : ∀ f, 0 ≤ reward f ∧ reward f ≤ 1) :
    let U := twoSidedExitUpTime X upper
    let L := twoSidedExitDownTime X lower
    let weightR := fun ω => if U ω < L ω then discount (U ω).toNNReal else 0
    let payoffR := fun ω => if U ω < L ω then discount (U ω).toNNReal * reward (fun s => X.X ((U ω).toNNReal + s) ω - X.X (U ω).toNNReal ω) else 0
    let rewR := fun ω => reward (fun s => X.X s ω)
    let discountE : ℝ≥0 → ℝ≥0∞ := fun t => ENNReal.ofReal (discount t)
    let rewardE : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun f => ENNReal.ofReal (reward f)
    (Integrable weightR P → Integrable payoffR P → Integrable rewR P →
     (∀ ω, 0 ≤ weightR ω) → (∀ ω, 0 ≤ payoffR ω) → (∀ ω, 0 ≤ rewR ω) →
     (ENNReal.ofReal (∫ ω, payoffR ω ∂P) = ∫⁻ ω, (if U ω < L ω then discountE ((U ω).toNNReal) * rewardE (fun t : ℝ≥0 => X.X ((U ω).toNNReal + t) ω - X.X ((U ω).toNNReal) ω) else 0) ∂P) ∧
     (ENNReal.ofReal (∫ ω, weightR ω ∂P) = ∫⁻ ω, (if U ω < L ω then discountE ((U ω).toNNReal) else 0) ∂P) ∧
     (ENNReal.ofReal (∫ ω, rewR ω ∂P) = ∫⁻ ω, rewardE (fun t : ℝ≥0 => X.X t ω) ∂P)) := by sorry
