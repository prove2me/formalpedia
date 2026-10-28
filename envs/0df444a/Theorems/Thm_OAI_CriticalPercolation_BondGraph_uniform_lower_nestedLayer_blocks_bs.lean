-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_uniform_lower_nestedLayer_blocks_bs
-- name    : OAI.CriticalPercolation.BondGraph.uniform_lower_nestedLayer_blocks_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:29:31.941376+00:00
-- url     : https://prove2.me/theorems/532ed841-0afa-421a-9cbe-00111cafa66e
-- title:
--   OAI.CriticalPercolation.BondGraph.uniform_lower_nestedLayer_blocks_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.uniform_lower_nestedLayer_blocks` of [lean/OAI/Probability/CriticalPercolation/Criticality/LayerLocality.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Criticality/LayerLocality.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory ProbabilityTheory Filter`, `open scoped Classical ENNReal Topology`):
--
--   ```lean
--   theorem uniform_lower_nestedLayer_blocks_bs
--       (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
--       (hu : ¬G.CombinatoriallyUnimodular) (o : V)
--       (p : unitInterval) (hp : 0<(p:ℝ)) (hp1 : (p:ℝ)<1)
--       (hper : 0<G.law p G.percolates)
--       (hm : ∀ v, ∀ᵐ ω ∂G.law p, G.modularMass v (G.cluster ω v)≠∞) :
--       ∃ R : ℕ, ∃ θ : ℝ, 0<θ ∧ ∃ M : ℕ, 1≤M ∧ ∀ a : ℝ, 0<a → ∀ N : ℕ,
--         ∃ δ : ℝ, 0<δ ∧ δ<1 ∧ δ<a ∧ ∃ q : unitInterval, 0<(q:ℝ) ∧ q<p ∧
--         ∀ T : ℝ, 0<T → ∀ x∈G.safeBallDomain o T R, a*T≤G.modularRatio x o →
--           θ<(G.law q).real (G.boundedDomainFreshExitEvent
--             (G.safeBallDomain o T R) (G.safeBallDomain o (δ*T) R)ᶜ x N M)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.CombinatoriallyUnimodular`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.boundedDomainFreshExitEvent`, `OAI.CriticalPercolation.BondGraph.cluster`, `OAI.CriticalPercolation.BondGraph.fullGraph`, `OAI.CriticalPercolation.BondGraph.law`, `OAI.CriticalPercolation.BondGraph.modularMass`, `OAI.CriticalPercolation.BondGraph.modularRatio`, `OAI.CriticalPercolation.BondGraph.percolates` and `OAI.CriticalPercolation.BondGraph.safeBallDomain` (definitions bundle `OAIQ078B000` of this split).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.nonunimodular_no_percolation_at_criticality_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Criticality/LayerLocality.lean (declaration OAI.CriticalPercolation.BondGraph.uniform_lower_nestedLayer_blocks)

import Mathlib
import Definitions.Def_OAIQ078B000

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem uniform_lower_nestedLayer_blocks_bs
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hu : ¬G.CombinatoriallyUnimodular) (o : V)
    (p : unitInterval) (hp : 0<(p:ℝ)) (hp1 : (p:ℝ)<1)
    (hper : 0<G.law p G.percolates)
    (hm : ∀ v, ∀ᵐ ω ∂G.law p, G.modularMass v (G.cluster ω v)≠∞) :
    ∃ R : ℕ, ∃ θ : ℝ, 0<θ ∧ ∃ M : ℕ, 1≤M ∧ ∀ a : ℝ, 0<a → ∀ N : ℕ,
      ∃ δ : ℝ, 0<δ ∧ δ<1 ∧ δ<a ∧ ∃ q : unitInterval, 0<(q:ℝ) ∧ q<p ∧
      ∀ T : ℝ, 0<T → ∀ x∈G.safeBallDomain o T R, a*T≤G.modularRatio x o →
        θ<(G.law q).real (G.boundedDomainFreshExitEvent
          (G.safeBallDomain o T R) (G.safeBallDomain o (δ*T) R)ᶜ x N M) := by
  sorry

end CriticalPercolation.BondGraph
end
end

end OAI
end
