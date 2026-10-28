-- Prove2me | Theorems.Thm_OAI_Percolation_integral_size_membership_le_bs
-- name    : OAI.Percolation.integral_size_membership_le_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:40:10.414892+00:00
-- url     : https://prove2.me/theorems/65d38f98-d508-482e-935c-1079adf1166f
-- title:
--   OAI.Percolation.integral_size_membership_le_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.integral_size_membership_le` of [lean/OAI/Probability/UnimodularPercolation/Deformation/ClusterProducts.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/Deformation/ClusterProducts.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`, `open MeasureTheory`):
--
--   ```lean
--   theorem integral_size_membership_le_bs (G : BondGraph V E) (hloc : LocallyFinite G)
--       (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) (x a : V) :
--       (∫ ω, (if Conn G ω x a then ((cluster G ω x).ncard:ℝ) else 0) ∂law p) ≤
--         maxSusceptibility G p * (∑' b, twoPoint G p x b * twoPoint G p b a)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.maxSusceptibility` (definitions bundle `OAIQ078B002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.Conn`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.QuasiTransitive`, `OAI.Percolation.cluster`, `OAI.Percolation.law`, `OAI.Percolation.pc` and `OAI.Percolation.twoPoint` (the published bundle `Def_BenjaminiSchramm`).
--
--   **Used by.** The proof of `OAI.Percolation.deformed_distinct_correlation_uniform_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/Deformation/ClusterProducts.lean (declaration OAI.Percolation.integral_size_membership_le)

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B002

section

attribute [-instance] _root_.OAI.Percolation.PointwisePerm.topology _root_.OAI.Percolation.graphAutBorelSpace _root_.OAI.Percolation.graphAutMeasurableSpace _root_.OAI.Percolation.graphAutSecondCountable _root_.OAI.Percolation.graphOrbitType_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section WeightedThreeArmEstimate
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

theorem integral_size_membership_le_bs (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) (x a : V) :
    (∫ ω, (if Conn G ω x a then ((cluster G ω x).ncard:ℝ) else 0) ∂law p) ≤
      maxSusceptibility G p * (∑' b, twoPoint G p x b * twoPoint G p b a) := by
  sorry

end WeightedThreeArmEstimate
end Percolation

end OAI
end
