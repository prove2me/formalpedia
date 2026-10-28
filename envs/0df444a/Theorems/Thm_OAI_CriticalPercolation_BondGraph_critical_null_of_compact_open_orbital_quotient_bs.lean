-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_critical_null_of_compact_open_orbital_quotient_bs
-- name    : OAI.CriticalPercolation.BondGraph.critical_null_of_compact_open_orbital_quotient_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:24:08.628657+00:00
-- url     : https://prove2.me/theorems/3f5bbde9-a6e1-4de0-aac7-45ceb6f1a42b
-- title:
--   OAI.CriticalPercolation.BondGraph.critical_null_of_compact_open_orbital_quotient_bs (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.critical_null_of_compact_open_orbital_quotient` of [lean/OAI/Probability/CriticalPercolation/GraphGeometry/FullOrbitalStructureTransfer.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/GraphGeometry/FullOrbitalStructureTransfer.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set Function MeasureTheory Topology`, `open scoped Classical ENNReal`):
--
--   ```lean
--   theorem critical_null_of_compact_open_orbital_quotient_bs
--       (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hg : G.SubexponentialGrowth)
--       (o : V) (L : ℕ) (hconn : (G.orbitPower o L).Connected)
--       (Λ : Subgroup G.Aut) [Group.FG Λ]
--       (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
--       (H : Subgroup (G.orbitPower o L ≃g G.orbitPower o L)) [H.Normal]
--       (N : Subgroup ((G.orbitPower o L ≃g G.orbitPower o L) ⧸ H)) [Group.IsNilpotent N]
--       (hN : N.index≠0)
--       (hH : let _ : TopologicalSpace (MulAction.orbit G.Aut o) := ⊥
--         let _ : TopologicalSpace (G.orbitPower o L ≃g G.orbitPower o L) :=
--           GraphTopology.autTopology (G.orbitPower o L)
--         IsCompact (H : Set (G.orbitPower o L ≃g G.orbitPower o L)) ∧
--         IsOpen (H : Set (G.orbitPower o L ≃g G.orbitPower o L)))
--       (hpc : G.criticalProbability<1) : G.law G.criticalProbability G.percolates=0
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.Aut`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.SubexponentialGrowth`, `OAI.CriticalPercolation.BondGraph.criticalProbability`, `OAI.CriticalPercolation.BondGraph.fullGraph`, `OAI.CriticalPercolation.BondGraph.instGroupAut`, `OAI.CriticalPercolation.BondGraph.instMulActionAut`, `OAI.CriticalPercolation.BondGraph.law`, `OAI.CriticalPercolation.BondGraph.orbitPower` and `OAI.CriticalPercolation.BondGraph.percolates` (definitions bundle `OAIQ078B000` of this split); `OAI.CriticalPercolation.GraphTopology.autTopology` (definitions bundle `OAIQ078B001` of this split).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.main_failure_topological_classification_counterexample_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/GraphGeometry/FullOrbitalStructureTransfer.lean (declaration OAI.CriticalPercolation.BondGraph.critical_null_of_compact_open_orbital_quotient)

import Mathlib
import Definitions.Def_OAIQ078B000
import Definitions.Def_OAIQ078B001

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Function MeasureTheory Topology
open scoped Classical ENNReal

namespace CriticalPercolation
namespace BondGraph
variable {V E : Type*} (G : BondGraph V E)

theorem critical_null_of_compact_open_orbital_quotient_bs
    (hc : G.fullGraph.Connected) (hl : G.LocallyFinite) (hg : G.SubexponentialGrowth)
    (o : V) (L : ℕ) (hconn : (G.orbitPower o L).Connected)
    (Λ : Subgroup G.Aut) [Group.FG Λ]
    (S : Set V) (hS : S.Finite) (hcover : ∀ v, ∃ s∈S, v∈MulAction.orbit Λ s)
    (H : Subgroup (G.orbitPower o L ≃g G.orbitPower o L)) [H.Normal]
    (N : Subgroup ((G.orbitPower o L ≃g G.orbitPower o L) ⧸ H)) [Group.IsNilpotent N]
    (hN : N.index≠0)
    (hH : let _ : TopologicalSpace (MulAction.orbit G.Aut o) := ⊥
      let _ : TopologicalSpace (G.orbitPower o L ≃g G.orbitPower o L) :=
        GraphTopology.autTopology (G.orbitPower o L)
      IsCompact (H : Set (G.orbitPower o L ≃g G.orbitPower o L)) ∧
      IsOpen (H : Set (G.orbitPower o L ≃g G.orbitPower o L)))
    (hpc : G.criticalProbability<1) : G.law G.criticalProbability G.percolates=0 := by
  sorry

end BondGraph
end CriticalPercolation
end
end

end OAI
end
