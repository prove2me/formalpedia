-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_Sharpness_critical_null_of_unique_bs
-- name    : OAI.CriticalPercolation.Sharpness.critical_null_of_unique_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:32:23.117243+00:00
-- url     : https://prove2.me/theorems/e018348f-17bb-4425-881d-c1a885e65dbb
-- title:
--   OAI.CriticalPercolation.Sharpness.critical_null_of_unique_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.Sharpness.critical_null_of_unique` of [lean/OAI/Probability/CriticalPercolation/Criticality/SubcriticalLocalRateBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Criticality/SubcriticalLocalRateBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.Sharpness`, with `open Set MeasureTheory Filter Topology`, `open scoped Classical BigOperators`):
--
--   ```lean
--   theorem critical_null_of_unique_bs (hc : G.fullGraph.Connected)
--       (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (o : V)
--       (γ : ℝ) (hγ : 0 < γ) (N : ℕ)
--       (hgrowth : ∀ m≥N, ∀ v : V, γ*m ≤ Real.log ((G.vertexBall v m).ncard : ℝ))
--       (hu : ∀ᵐ ω ∂G.law G.criticalProbability, ∀ x y, (G.cluster ω x).Infinite →
--         (G.cluster ω y).Infinite → (G.openGraph ω).Reachable x y) :
--       G.law G.criticalProbability G.percolates = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.cluster`, `OAI.CriticalPercolation.BondGraph.criticalProbability`, `OAI.CriticalPercolation.BondGraph.fullGraph`, `OAI.CriticalPercolation.BondGraph.law`, `OAI.CriticalPercolation.BondGraph.openGraph`, `OAI.CriticalPercolation.BondGraph.percolates` and `OAI.CriticalPercolation.BondGraph.vertexBall` (definitions bundle `OAIQ078B000` of this split).
--
--   **Used by.** The proofs of `OAI.CriticalPercolation.BondGraph.CombinatoriallyUnimodular.exponential_critical_null_bs` and `OAI.CriticalPercolation.BondGraph.main_light_or_sparse_polynomial_boundary_bs` of this split import it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Criticality/SubcriticalLocalRateBound.lean (declaration OAI.CriticalPercolation.Sharpness.critical_null_of_unique)

import Mathlib
import Definitions.Def_OAIQ078B000

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section CurrentModule13

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

theorem critical_null_of_unique_bs (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (o : V)
    (γ : ℝ) (hγ : 0 < γ) (N : ℕ)
    (hgrowth : ∀ m≥N, ∀ v : V, γ*m ≤ Real.log ((G.vertexBall v m).ncard : ℝ))
    (hu : ∀ᵐ ω ∂G.law G.criticalProbability, ∀ x y, (G.cluster ω x).Infinite →
      (G.cluster ω y).Infinite → (G.openGraph ω).Reachable x y) :
    G.law G.criticalProbability G.percolates = 0 := by
  sorry

end CriticalPercolation.Sharpness
end
end CurrentModule13

end

end OAI
end
