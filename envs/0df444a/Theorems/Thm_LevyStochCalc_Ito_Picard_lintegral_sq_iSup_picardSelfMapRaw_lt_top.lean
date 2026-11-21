-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_lintegral_sq_iSup_picardSelfMapRaw_lt_top
-- name    : LevyStochCalc.Ito.Picard.lintegral_sq_iSup_picardSelfMapRaw_lt_top
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:11:29.048173+00:00
-- url     : https://prove2.me/theorems/74d48a27-5fd6-41a8-be09-20aebc4a3790
-- title:
--   lintegral sq iSup picardSelfMapRaw lt top
-- statement:
--   The source theorem `LevyStochCalc.Ito.Picard.lintegral_sq_iSup_picardSelfMapRaw_lt_top` is extracted from `LevyStochCalc.Ito.PicardSupL2`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F000
import Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F001
import Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F002
import Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F003
import Definitions.Def_LevyStochCalc_Ito_PicardContractionEstimate_F004
import Definitions.Def_LevyStochCalc_Ito_PicardContractionFixedPoint_F000
import Definitions.Def_LevyStochCalc_Ito_PicardContractionFixedPoint_F001
import Definitions.Def_LevyStochCalc_Ito_PicardContractionFixedPoint_F002
import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F002
import Definitions.Def_LevyStochCalc_Probability_DoobContinuous_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The `S²` bound for the Picard step

`LevyStochCalc.Ito.Setting.JumpDiffusion.sup_L2` asks for `𝔼[sup_{t ≤ T} ‖X_t‖²] < ∞`, the `S²`
norm, which is stronger than the weighted supremum of `L²` norms the Picard space carries. The
Picard step splits into a drift, `d` Brownian integrals and a compensated-Poisson integral; the
drift is bounded pathwise by its own total variation over the window, and each stochastic
component is a martingale, so Doob's `L²` inequality over the dyadic points applies. Only the
dyadic form of Doob is available here, because the stochastic integrals are càdlàg only up to
modification.
-/

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-! ### An elementary two-term bound -/

/-! ### The drift component -/

/-! ### The stochastic components -/

variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]

/-! ### The whole step -/

/-! ### The `S²` bound for the raw self-map -/

theorem _root_.LevyStochCalc.Ito.Picard.lintegral_sq_iSup_picardSelfMapRaw_lt_top
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {T : ℝ} (hT : 0 < T)
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z))
    (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hZb : bieleckiNorm (P := P) 0 T Z < ⊤) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i,
        (‖(picardSelfMapRaw W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT hZm hZa hZb).X
          (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ := by sorry
