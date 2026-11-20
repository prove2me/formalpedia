-- Prove2me | Theorems.Thm_LevyStochCalc_Probability_indep_comap_of_tendsto_ae
-- name    : LevyStochCalc.Probability.indep_comap_of_tendsto_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:35:17.501377+00:00
-- url     : https://prove2.me/theorems/4247d076-674e-4567-9ddb-c08a6da96432
-- title:
--   indep comap of tendsto ae
-- statement:
--   The source theorem `LevyStochCalc.Probability.indep_comap_of_tendsto_ae` is extracted from `LevyStochCalc.Probability.IndepLimit`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Probability_IndepLimit_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Independence survives almost-everywhere limits

If each random variable `X n` is independent of a σ-algebra `m` and `X n → Y` almost
everywhere, then `Y` is independent of `m`: for a set `A ∈ m` the laws of `Y` under `P|_A` and
under `P(A) • P` have the same integrals against bounded continuous functions, by dominated
convergence, hence coincide.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BoundedContinuousFunction

namespace LevyStochCalc.Probability

variable {Ω 𝓧 : Type*} {m mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  [TopologicalSpace 𝓧] [MeasurableSpace 𝓧] [BorelSpace 𝓧] [HasOuterApproxClosed 𝓧]

theorem _root_.LevyStochCalc.Probability.indep_comap_of_tendsto_ae (hm : m ≤ mΩ) {X : ℕ → Ω → 𝓧}
    {Y : Ω → 𝓧} (hX : ∀ n, Measurable[mΩ] (X n)) (hY : Measurable[mΩ] Y)
    (hind : ∀ n, Indep m (MeasurableSpace.comap (X n) inferInstance) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Indep m (MeasurableSpace.comap Y inferInstance) P := by sorry
