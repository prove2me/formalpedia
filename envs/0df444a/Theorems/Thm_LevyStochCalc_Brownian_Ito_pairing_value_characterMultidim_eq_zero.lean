-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_pairing_value_characterMultidim_eq_zero
-- name    : LevyStochCalc.Brownian.Ito.pairing_value_characterMultidim_eq_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T20:21:15.765646+00:00
-- url     : https://prove2.me/theorems/49251ce3-6c32-4900-8a13-bc8ebdc033d1
-- title:
--   pairing value characterMultidim eq zero
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.pairing_value_characterMultidim_eq_zero` is extracted from `LevyStochCalc.Brownian.PRPMultidim`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_PRPMultidim_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# One window of the multidimensional Brownian predictable representation

A weight orthogonal to every coordinate's Itô integrals is orthogonal to the integrals against
any unit linear combination of the coordinates, so the one-window statement transfers, and a
multidimensional cell character is a scalar character of the combination.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

theorem _root_.LevyStochCalc.Brownian.Ito.pairing_value_characterMultidim_eq_zero (W : Multidim.MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (hℱB : ∀ {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1),
      IsBrownianFiltration (Multidim.MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {τ : ℕ → ℝ} (hτ0 : τ 0 = 0)
    {Z : Ω → ℂ} (hZm : Measurable Z) (hZ2 : MemLp Z 2 P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) ℱ (hℱi i) Z)
    (hZ0 : ∫ ω, Z ω ∂P = 0) (c : ℕ → Fin d → ℝ) (n : ℕ)
    (hlt : ∀ k, k < n → τ k < τ (k + 1)) :
    ∫ ω, Z ω * Complex.exp (((∑ i, ∑ k ∈ Finset.Ico 1 (n + 1),
      c k i * (W.W i).W (τ k) ω : ℝ) : ℂ) * Complex.I) ∂P = 0 := by sorry
