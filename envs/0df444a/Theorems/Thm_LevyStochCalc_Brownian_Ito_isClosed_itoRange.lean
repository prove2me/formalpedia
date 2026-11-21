-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_isClosed_itoRange
-- name    : LevyStochCalc.Brownian.Ito.isClosed_itoRange
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:49:56.196933+00:00
-- url     : https://prove2.me/theorems/a7df99f5-7cfd-4acf-864f-5cb7d1efbf4d
-- title:
--   isClosed itoRange
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.isClosed_itoRange` is extracted from `LevyStochCalc.Brownian.ItoRange`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoRange_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The range of the Itô integral on a horizon

An integrand supported in `[0, T]`, jointly and progressively measurable and of finite energy,
is admissible for the Itô integral up to `T`. Such integrands are closed under sums and scalar
multiples, and the integral is additive and homogeneous on them, so their integrals form a
submodule of `L²`. The isometry of differences carries an energy-Cauchy sequence of integrands to
an `L²`-Cauchy sequence of integrals, so that submodule is closed.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Energy

variable {T : ℝ}

end Energy

namespace HorizonIntegrand

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

section Integral

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)

end Integral

end HorizonIntegrand

section Range

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)

theorem _root_.LevyStochCalc.Brownian.Ito.isClosed_itoRange (hT : 0 < T) :
    IsClosed ((itoRange W hℱ hT : Submodule ℝ (Lp ℝ 2 P)) : Set (Lp ℝ 2 P)) := by sorry
