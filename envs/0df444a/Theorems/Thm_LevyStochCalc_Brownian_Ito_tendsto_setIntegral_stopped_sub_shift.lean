-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_tendsto_setIntegral_stopped_sub_shift
-- name    : LevyStochCalc.Brownian.Ito.tendsto_setIntegral_stopped_sub_shift
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:39:29.616198+00:00
-- url     : https://prove2.me/theorems/2a9db0dc-6868-4321-920e-06a9cc03aa05
-- title:
--   tendsto setIntegral stopped sub shift
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.tendsto_setIntegral_stopped_sub_shift` is extracted from `LevyStochCalc.Ito.ItoFormulaRandomShift`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoCutoff_F003
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaIncrement_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Passing to the limit in a shifted Itô formula

A shift of the argument of a `C²` function by a random vector is approximated by shifts along a
sequence of random vectors converging to it pointwise. Each term of the resulting identity
converges: the boundary term by continuity of the function, the two Lebesgue terms by dominated
convergence along the path, and the stochastic term in `L²` by the difference isometry, hence
almost surely along a subsequence. An identity holding for every member of the sequence therefore
holds in the limit.

## Main statements

* `LevyStochCalc.Brownian.Ito.stopped_sub` — cutting off at a stopping time is linear.
* `LevyStochCalc.Brownian.Ito.tendsto_lintegral_sq_comp_shift` — the energy of the difference of
  two shifted integrands vanishes along a pointwise-convergent sequence of shifts.
* `LevyStochCalc.Brownian.Ito.tendsto_setIntegral_stopped_sub_shift` — the Lebesgue terms
  converge along the path.
* `LevyStochCalc.Brownian.Ito.ae_eq_of_tendsto_of_forall_ae_eq` — an almost-everywhere identity
  survives an almost-everywhere limit on both sides.
* `LevyStochCalc.Brownian.Ito.tendsto_lintegral_sq_stochInt_of_tendsto_energy` — a vanishing
  energy distance between integrands gives a vanishing `L²` distance between their Itô integrals.
* `LevyStochCalc.Brownian.Ito.exists_seq_ae_tendsto_stochInt_of_tendsto_energy` — the same over
  finitely many Brownian channels, almost surely along a common subsequence.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {α : Type*}

section StoppedAlgebra

variable {Ω : Type*}

end StoppedAlgebra

section LimitTransfer

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

end LimitTransfer

section Energy

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end Energy

section PathIntegral

variable {Ω : Type u}

theorem _root_.LevyStochCalc.Brownian.Ito.tendsto_setIntegral_stopped_sub_shift {n : ℕ} {X : ℝ → Ω → Fin n → ℝ}
    {g : (Fin n → ℝ) → ℝ} (hgc : Continuous g) {K : ℝ} (hK : ∀ z, |g z| ≤ K)
    {D : Ω → ℝ → ℝ} {σ τ : Ω → WithTop ℝ} {T : ℝ} {ω : Ω}
    {c : Ω → Fin n → ℝ} {cm : ℕ → Ω → Fin n → ℝ}
    (hlim : Filter.Tendsto (fun m => cm m ω) Filter.atTop (nhds (c ω)))
    (hint : IntegrableOn (fun s => D ω s) (Set.Ioc (0 : ℝ) T) volume)
    (hmeas : ∀ m : ℕ, AEStronglyMeasurable (fun s =>
        Probability.stopped τ (fun ω s => g (X s ω + cm m ω) * D ω s) ω s
          - Probability.stopped σ (fun ω s => g (X s ω + cm m ω) * D ω s) ω s)
      (volume.restrict (Set.Ioc (0 : ℝ) T))) :
    Filter.Tendsto (fun m => ∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped τ (fun ω s => g (X s ω + cm m ω) * D ω s) ω s
          - Probability.stopped σ (fun ω s => g (X s ω + cm m ω) * D ω s) ω s) ∂volume)
      Filter.atTop (nhds (∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped τ (fun ω s => g (X s ω + c ω) * D ω s) ω s
          - Probability.stopped σ (fun ω s => g (X s ω + c ω) * D ω s) ω s) ∂volume)) := by sorry
