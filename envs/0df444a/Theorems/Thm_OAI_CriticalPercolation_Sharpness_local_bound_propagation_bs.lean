-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_Sharpness_local_bound_propagation_bs
-- name    : OAI.CriticalPercolation.Sharpness.local_bound_propagation_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:36:04.685709+00:00
-- url     : https://prove2.me/theorems/252b1c4c-f926-4467-bcd6-72d120c94448
-- title:
--   OAI.CriticalPercolation.Sharpness.local_bound_propagation_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.Sharpness.local_bound_propagation` of [lean/OAI/Probability/CriticalPercolation/Criticality/TwoPointSelf.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Criticality/TwoPointSelf.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.Sharpness`, with `open Set MeasureTheory Filter Topology`, `open scoped Classical BigOperators`):
--
--   ```lean
--   lemma local_bound_propagation_bs [Countable V] [Countable E] (p : unitInterval)
--       (n : ℕ) (a : ℝ) (ha : 0 ≤ a)
--       (hlocal : ∀ x y : V, y ∈ G.vertexBall x n → a ≤ twoPoint G p x y) :
--       ∀ (k : ℕ) (x y : V), y ∈ G.vertexBall x (k*n) → a^k ≤ twoPoint G p x y
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph` and `OAI.CriticalPercolation.BondGraph.vertexBall` (definitions bundle `OAIQ078B000` of this split); `OAI.CriticalPercolation.Sharpness.twoPoint` (definitions bundle `OAIQ078B002` of this split).
--
--   **Used by.** The proofs of `OAI.CriticalPercolation.BondGraph.nonunimodular_critical_mass_finite_ae_bs` and `OAI.CriticalPercolation.Sharpness.critical_null_of_unique_bs` of this split import it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Criticality/TwoPointSelf.lean (declaration OAI.CriticalPercolation.Sharpness.local_bound_propagation)

import Mathlib
import Definitions.Def_OAIQ078B002

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section CurrentModule11
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
variable {V E : Type*} (G : BondGraph V E)

lemma local_bound_propagation_bs [Countable V] [Countable E] (p : unitInterval)
    (n : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hlocal : ∀ x y : V, y ∈ G.vertexBall x n → a ≤ twoPoint G p x y) :
    ∀ (k : ℕ) (x y : V), y ∈ G.vertexBall x (k*n) → a^k ≤ twoPoint G p x y := by
  sorry

end CriticalPercolation.Sharpness
end
end CurrentModule11

end

end OAI
end
