-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_martingale_simpleIntegral_brownian
-- name    : LevyStochCalc.Brownian.Ito.martingale_simpleIntegral_brownian
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T16:14:41.298291+00:00
-- url     : https://prove2.me/theorems/12ed1112-f405-41e8-8f1d-c1b0c24cc921
-- title:
--   martingale simpleIntegral brownian
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.martingale_simpleIntegral_brownian` is extracted from `LevyStochCalc.Brownian.ItoMartingale`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoMartingale_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Martingale property of the simple Brownian integral

`simpleIntegral W H` is a martingale w.r.t. any filtration `ℱ` for which `W` is a
Brownian motion and `H` is adapted (`martingale_simpleIntegral_brownian`), via the
conditional-expectation identity for `W`. Builds on `Brownian/ItoSimple.lean` and
`Brownian/ItoDensity.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

theorem _root_.LevyStochCalc.Brownian.Ito.martingale_simpleIntegral_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    MeasureTheory.Martingale (fun t : ℝ => simpleIntegral W H t)
      ℱ P := by sorry
