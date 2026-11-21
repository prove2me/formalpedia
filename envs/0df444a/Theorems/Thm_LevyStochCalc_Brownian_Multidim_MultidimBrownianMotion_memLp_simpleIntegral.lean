-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_memLp_simpleIntegral
-- name    : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_simpleIntegral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:22:19.916176+00:00
-- url     : https://prove2.me/theorems/8338133c-8ceb-43f1-bcfb-df758fc0d141
-- title:
--   memLp simpleIntegral
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_simpleIntegral` is extracted from `LevyStochCalc.Brownian.CrossOrthogonalityLimit`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityLimit_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Orthogonality of Itô integrals against distinct Brownian coordinates

Cross terms over intervals in any relative position reduce to the direct cross identity by
splitting at the later left endpoint, so elementary integrals against two distinct coordinates
`Wⁱ` and `Wʲ` of a `d`-dimensional Brownian motion have zero pairing. Continuity of the `L²`
pairing carries that vanishing to the limit along approximating simple integrands, giving the
orthogonality in `L²` of the Itô integrals against `Wⁱ` and against `Wʲ`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

namespace Multidim.MultidimBrownianMotion

section SimpleIntegrands

open LevyStochCalc.Brownian.Ito

variable {W : MultidimBrownianMotion P d}

end SimpleIntegrands

section L2Limit

open LevyStochCalc.Brownian.Ito

theorem _root_.LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_simpleIntegral (V : BrownianMotion P) {T : ℝ} (G : SimplePredictable Ω T) (t : ℝ) :
    MemLp (fun ω => simpleIntegral V G t ω) 2 P := by sorry
