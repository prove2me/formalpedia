-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_normalized_crossing_exponent_approximation_bs
-- name    : OAI.CriticalPercolation.BondGraph.normalized_crossing_exponent_approximation_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:28:53.469439+00:00
-- url     : https://prove2.me/theorems/8e86f810-93fc-4db7-8f5c-33b08e95f77d
-- title:
--   OAI.CriticalPercolation.BondGraph.normalized_crossing_exponent_approximation_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.normalized_crossing_exponent_approximation` of [lean/OAI/Probability/BenjaminiSchramm/CrossingExponentContinuity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/CrossingExponentContinuity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory Filter`, `open scoped Classical ENNReal Topology`, `open Percolation.BenjaminiSchramm`):
--
--   ```lean
--   theorem normalized_crossing_exponent_approximation_bs [Fintype G.VertexOrbit] [Nontrivial V]
--       [Encodable V] [Countable E]
--       (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
--       (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
--       (hstat : orbitChainStep (G.orbitWalkKernel hl) μ = μ) (hu : ¬ G.CombinatoriallyUnimodular)
--       (p : unitInterval) (hp : 0 < p) (α : ℝ)
--       (hlim : Tendsto (fun n : ℕ => -Real.log
--         (G.infimalAdjustedCrossing (G.stationaryOrbitWeight μ) p n).toReal/n) atTop (𝓝 α))
--       (ε : ℝ) (hε : 0 < ε) :
--       ∃ q : unitInterval, (p : ℝ)/2 ≤ q ∧ q < p ∧ ∃ β : ℝ, 0 ≤ β ∧ β < α+ε ∧
--         (∀ n : ℕ, (G.infimalAdjustedCrossing (G.stationaryOrbitWeight μ) q n).toReal ≤ Real.exp (-β*n)) ∧
--         (∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
--           c*Real.exp (-(β+δ)*n) ≤ (G.infimalAdjustedCrossing (G.stationaryOrbitWeight μ) q n).toReal)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.CombinatoriallyUnimodular`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.VertexOrbit`, `OAI.CriticalPercolation.BondGraph.fullGraph`, `OAI.CriticalPercolation.BondGraph.infimalAdjustedCrossing`, `OAI.CriticalPercolation.BondGraph.orbitWalkKernel` and `OAI.CriticalPercolation.BondGraph.stationaryOrbitWeight` (definitions bundle `OAIQ078B000` of this split); `OAI.Percolation.BenjaminiSchramm.orbitChainStep` (definitions bundle `OAIQ078B001` of this split).
--
--   **Used by.** The proof of `OAI.Percolation.BenjaminiSchramm.critical_lower_slab_fractional_profile_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/CrossingExponentContinuity.lean (declaration OAI.CriticalPercolation.BondGraph.normalized_crossing_exponent_approximation)

import Mathlib
import Definitions.Def_OAIQ078B000
import Definitions.Def_OAIQ078B001

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Classical ENNReal Topology

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} (G : BondGraph V E)

theorem normalized_crossing_exponent_approximation_bs [Fintype G.VertexOrbit] [Nontrivial V]
    [Encodable V] [Countable E]
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ = μ) (hu : ¬ G.CombinatoriallyUnimodular)
    (p : unitInterval) (hp : 0 < p) (α : ℝ)
    (hlim : Tendsto (fun n : ℕ => -Real.log
      (G.infimalAdjustedCrossing (G.stationaryOrbitWeight μ) p n).toReal/n) atTop (𝓝 α))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ q : unitInterval, (p : ℝ)/2 ≤ q ∧ q < p ∧ ∃ β : ℝ, 0 ≤ β ∧ β < α+ε ∧
      (∀ n : ℕ, (G.infimalAdjustedCrossing (G.stationaryOrbitWeight μ) q n).toReal ≤ Real.exp (-β*n)) ∧
      (∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ,
        c*Real.exp (-(β+δ)*n) ≤ (G.infimalAdjustedCrossing (G.stationaryOrbitWeight μ) q n).toReal) := by
  sorry

end CriticalPercolation.BondGraph

end

end OAI
end
