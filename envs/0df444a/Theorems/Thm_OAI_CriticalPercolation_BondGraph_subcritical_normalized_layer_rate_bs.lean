-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_subcritical_normalized_layer_rate_bs
-- name    : OAI.CriticalPercolation.BondGraph.subcritical_normalized_layer_rate_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:29:54.103355+00:00
-- url     : https://prove2.me/theorems/b27b69f9-0260-4e24-b65b-38d7266e3168
-- title:
--   OAI.CriticalPercolation.BondGraph.subcritical_normalized_layer_rate_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.subcritical_normalized_layer_rate` of [lean/OAI/Probability/BenjaminiSchramm/LayerFirstMomentRate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/LayerFirstMomentRate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set MeasureTheory Filter`, `open scoped Classical ENNReal Topology`, `open Percolation.BenjaminiSchramm`):
--
--   ```lean
--   theorem subcritical_normalized_layer_rate_bs
--       (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
--       (hql : Percolation.QuasiTransitive G.ends)
--       (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
--       (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ) (hu : ¬G.CombinatoriallyUnimodular)
--       (R : ℝ) (hR : 0 < R)
--       (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
--         |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R)
--       (p : unitInterval) (hp : 0 < (p : ℝ)) (hpc : p < Percolation.pc G.ends) :
--       ∃ β : ℝ, 0 ≤ β ∧
--         (∀ n : ℕ, Real.exp (-β*n) ≤
--           (G.supAdjustedUpLayerMoment (G.stationaryOrbitWeight μ) R p n).toReal) ∧
--         (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
--           G.supAdjustedUpLayerMoment (G.stationaryOrbitWeight μ) R p n ≤
--             ENNReal.ofReal (K*Real.exp (-(β-ε)*n))) ∧
--         Tendsto (fun n : ℕ => -Real.log
--           (G.supAdjustedUpLayerMoment (G.stationaryOrbitWeight μ) R p n).toReal/n) atTop (𝓝 β)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.CombinatoriallyUnimodular`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.QuasiTransitive`, `OAI.CriticalPercolation.BondGraph.VertexOrbit`, `OAI.CriticalPercolation.BondGraph.fullGraph`, `OAI.CriticalPercolation.BondGraph.orbitAdjustedHeight`, `OAI.CriticalPercolation.BondGraph.orbitWalkKernel`, `OAI.CriticalPercolation.BondGraph.stationaryOrbitWeight` and `OAI.CriticalPercolation.BondGraph.supAdjustedUpLayerMoment` (definitions bundle `OAIQ078B000` of this split); `OAI.Percolation.BenjaminiSchramm.orbitChainStep` (definitions bundle `OAIQ078B001` of this split); `OAI.Percolation.QuasiTransitive` and `OAI.Percolation.pc` (the published bundle `Def_BenjaminiSchramm`).
--
--   **Used by.** The proof of `OAI.Percolation.BenjaminiSchramm.subcritical_layer_prefactor_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BenjaminiSchramm/LayerFirstMomentRate.lean (declaration OAI.CriticalPercolation.BondGraph.subcritical_normalized_layer_rate)

import Mathlib
import Definitions.Def_BenjaminiSchramm
import Definitions.Def_OAIQ078B000
import Definitions.Def_OAIQ078B001

section

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
variable {V E : Type*} [Countable V] [Countable E] [Nontrivial V]
  (G : BondGraph V E) [Fintype G.VertexOrbit]

theorem subcritical_normalized_layer_rate_bs
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hql : Percolation.QuasiTransitive G.ends)
    (μ : G.VertexOrbit → ℝ) (hμ : ∀ i, 0 < μ i)
    (hstat : orbitChainStep (G.orbitWalkKernel hl) μ=μ) (hu : ¬G.CombinatoriallyUnimodular)
    (R : ℝ) (hR : 0 < R)
    (hjump : ∀ e v w, v ∈ G.ends e → w ∈ G.ends e →
      |G.orbitAdjustedHeight (G.stationaryOrbitWeight μ) v w| ≤ R)
    (p : unitInterval) (hp : 0 < (p : ℝ)) (hpc : p < Percolation.pc G.ends) :
    ∃ β : ℝ, 0 ≤ β ∧
      (∀ n : ℕ, Real.exp (-β*n) ≤
        (G.supAdjustedUpLayerMoment (G.stationaryOrbitWeight μ) R p n).toReal) ∧
      (∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
        G.supAdjustedUpLayerMoment (G.stationaryOrbitWeight μ) R p n ≤
          ENNReal.ofReal (K*Real.exp (-(β-ε)*n))) ∧
      Tendsto (fun n : ℕ => -Real.log
        (G.supAdjustedUpLayerMoment (G.stationaryOrbitWeight μ) R p n).toReal/n) atTop (𝓝 β) := by
  sorry

end CriticalPercolation.BondGraph

end

end OAI
end
