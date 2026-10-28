-- Prove2me | Theorems.Thm_OAI_Percolation_twoPoint_double_restricted_bound_bs
-- name    : OAI.Percolation.twoPoint_double_restricted_bound_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:42:14.974099+00:00
-- url     : https://prove2.me/theorems/ebedf133-3d91-49c4-925a-723ea14c7966
-- title:
--   OAI.Percolation.twoPoint_double_restricted_bound_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.twoPoint_double_restricted_bound` of [lean/OAI/Probability/UnimodularPercolation/Deformation/ClusterProducts.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/Deformation/ClusterProducts.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`):
--
--   ```lean
--   theorem twoPoint_double_restricted_bound_bs (G : BondGraph V E) (hloc : LocallyFinite G)
--       (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) (x : V) (N : Set V) :
--       (∑' y : V, ∑' z : N, twoPoint G p x z * twoPoint G p z y) ≤
--         maxSusceptibility G p * (∑' z : N, twoPoint G p x z)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.maxSusceptibility` (definitions bundle `OAIQ078B002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.QuasiTransitive`, `OAI.Percolation.pc` and `OAI.Percolation.twoPoint` (the published bundle `Def_BenjaminiSchramm`).
--
--   **Used by.** The proofs of `OAI.Percolation.deformed_distinct_correlation_uniform_bs` and `OAI.Percolation.exists_finite_scale_obstruction_bs` of this split import it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/Deformation/ClusterProducts.lean (declaration OAI.Percolation.twoPoint_double_restricted_bound)

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
section DeletionSusceptibilityEstimate
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

theorem twoPoint_double_restricted_bound_bs (G : BondGraph V E) (hloc : LocallyFinite G)
    (hqt : QuasiTransitive G) (p : unitInterval) (hp : p < pc G) (x : V) (N : Set V) :
    (∑' y : V, ∑' z : N, twoPoint G p x z * twoPoint G p z y) ≤
      maxSusceptibility G p * (∑' z : N, twoPoint G p x z) := by
  sorry

end DeletionSusceptibilityEstimate
end Percolation

end OAI
end
