-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_BigJump_stochasticIntegral_markCut_add_compl
-- name    : LevyStochCalc.Ito.BigJump.stochasticIntegral_markCut_add_compl
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:32:32.362193+00:00
-- url     : https://prove2.me/theorems/03d0d0d0-68d0-469f-9fae-c73689e1a6e9
-- title:
--   stochasticIntegral markCut add compl
-- statement:
--   The source theorem `LevyStochCalc.Ito.BigJump.stochasticIntegral_markCut_add_compl` is extracted from `LevyStochCalc.Ito.BigJumpDiffusion`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Theorems.Thm_LevyStochCalc_Probability_MarkedProgressivelyMeasurable_indicator_mark
import Definitions.Def_LevyStochCalc_Ito_BigJumpDiffusion_F000
import Definitions.Def_LevyStochCalc_Ito_BigJumpDiffusion_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Truncating the jumps of a jump diffusion at one mark set

Restricting the jump coefficient of a jump diffusion to a measurable set of marks `A` splits it
into two coefficient bundles, and the compensated integral of an admissible integrand splits
accordingly. Subtracting the everywhere-càdlàg modification of the compensated integral over `A`
from the path leaves the *big-jump path*, which carries the drift, the diffusion and the jumps
outside `A`.

## Main definitions

* `LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.markCutγ` — the coefficient bundle with the jump
  coefficient restricted to a set of marks.
* `LevyStochCalc.Ito.BigJump.SdeData` — the filtration and admissibility data with which a jump
  diffusion satisfies its SDE.
* `LevyStochCalc.Ito.BigJump.cutJumpIntegral` — the everywhere-càdlàg modification of the
  compensated integral of the jump coefficient restricted to a set of marks.
* `LevyStochCalc.Ito.BigJump.bigJumpPath` — the path with that integral subtracted.

## Main statements

* `LevyStochCalc.Ito.BigJump.stochasticIntegral_markCut_add_compl` — the compensated integral of
  an integrand is the sum of the compensated integrals of its two mark cuts.
* `LevyStochCalc.Ito.BigJump.lintegral_sq_iSup_bigJumpPath_lt_top` — the big-jump path has
  square-integrable supremum over every bounded window.
* `LevyStochCalc.Ito.BigJump.isItoLevyProcess_bigJumpPath` — the big-jump path is an Itô–Lévy
  process whose drift and diffusion are those of the jump diffusion along its own path and whose
  jump integrand is the jump coefficient restricted to the complement of the cut.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Poisson.Compensated

namespace LevyStochCalc.Ito.Setting

universe v

variable {n d : ℕ} {E : Type v}

end LevyStochCalc.Ito.Setting

namespace LevyStochCalc.Ito.BigJump

universe u v

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.SmallJump

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ}

section Split

variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)

include hℱ in

theorem _root_.LevyStochCalc.Ito.BigJump.stochasticIntegral_markCut_add_compl (φ : Ω → ℝ → E → ℝ)
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {A : Set E} (hA : MeasurableSet A) (T : ℝ) :
    stochasticIntegral N ℱ hℱ φ hm hp hq T
      =ᵐ[P] fun ω => stochasticIntegral N ℱ hℱ (markCut A φ)
            (measurable_markCut hm hA) (hp.indicator_mark hA)
            (fun T' hT' => sq_markCut hq A T' hT') T ω
          + stochasticIntegral N ℱ hℱ (markCut Aᶜ φ)
            (measurable_markCut hm hA.compl) (hp.indicator_mark hA.compl)
            (fun T' hT' => sq_markCut hq Aᶜ T' hT') T ω := by sorry
