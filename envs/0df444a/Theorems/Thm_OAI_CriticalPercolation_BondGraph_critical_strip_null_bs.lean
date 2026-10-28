-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_critical_strip_null_bs
-- name    : OAI.CriticalPercolation.BondGraph.critical_strip_null_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:23:38.258056+00:00
-- url     : https://prove2.me/theorems/6c1943e7-e769-4df4-a396-e2563c5b2906
-- title:
--   OAI.CriticalPercolation.BondGraph.critical_strip_null_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.critical_strip_null` of [lean/OAI/Probability/CriticalPercolation/GraphGeometry/StripCritical.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/GraphGeometry/StripCritical.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set Function MeasureTheory ProbabilityTheory Filter`, `open scoped Classical Topology ENNReal`):
--
--   ```lean
--   theorem critical_strip_null_bs (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
--       (hq : G.QuasiTransitive) (hg : G.SubexponentialGrowth)
--       (hpc1 : G.criticalProbability<1)
--       (u v : V → ℝ) (o : V) (c : ℕ) (D : ℝ)
--       (hD : 0≤D) (huo : u o=0) (hvo : v o=0)
--       (hu : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |u x-u y|≤D)
--       (hv : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |v x-v y|≤D)
--       (hvunbounded : ∀ n : ℕ, ∃ x, (n : ℝ)<v x)
--       (hdense : ∀ y, ∃ φ : G.Aut, φ.vertex o∈G.vertexBall y c ∧
--         (∀ x y, u (φ.vertex x)-u (φ.vertex y)=u x-u y) ∧
--         (∀ x y, v (φ.vertex x)-v (φ.vertex y)=v x-v y))
--       (hnoray : ∀ᵐ ω ∂G.law G.criticalProbability,
--         ¬∃ r : G.OpenRay ω, ∃ U W : ℝ, ∀ n, |u (r.vertex n)|≤U ∧ |v (r.vertex n)|≤W) :
--       G.law G.criticalProbability (G.someStripPercolates v)=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.Aut`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.OpenRay`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.SubexponentialGrowth`, `OAI.CriticalPercolation.BondGraph.criticalProbability`, `OAI.CriticalPercolation.BondGraph.fullGraph`, `OAI.CriticalPercolation.BondGraph.law`, `OAI.CriticalPercolation.BondGraph.someStripPercolates` and `OAI.CriticalPercolation.BondGraph.vertexBall` (definitions bundle `OAIQ078B000` of this split).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.critical_null_of_action_coordinates_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/GraphGeometry/StripCritical.lean (declaration OAI.CriticalPercolation.BondGraph.critical_strip_null)

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
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem critical_strip_null_bs (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (hg : G.SubexponentialGrowth)
    (hpc1 : G.criticalProbability<1)
    (u v : V → ℝ) (o : V) (c : ℕ) (D : ℝ)
    (hD : 0≤D) (huo : u o=0) (hvo : v o=0)
    (hu : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |u x-u y|≤D)
    (hv : ∀ ⦃x y⦄, G.fullGraph.Adj x y → |v x-v y|≤D)
    (hvunbounded : ∀ n : ℕ, ∃ x, (n : ℝ)<v x)
    (hdense : ∀ y, ∃ φ : G.Aut, φ.vertex o∈G.vertexBall y c ∧
      (∀ x y, u (φ.vertex x)-u (φ.vertex y)=u x-u y) ∧
      (∀ x y, v (φ.vertex x)-v (φ.vertex y)=v x-v y))
    (hnoray : ∀ᵐ ω ∂G.law G.criticalProbability,
      ¬∃ r : G.OpenRay ω, ∃ U W : ℝ, ∀ n, |u (r.vertex n)|≤U ∧ |v (r.vertex n)|≤W) :
    G.law G.criticalProbability (G.someStripPercolates v)=0 := by
  sorry

end CriticalPercolation.BondGraph
end
end
end

end OAI
end
