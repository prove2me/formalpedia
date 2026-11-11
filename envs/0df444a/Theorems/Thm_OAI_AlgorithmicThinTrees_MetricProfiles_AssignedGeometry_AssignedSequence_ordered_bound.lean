-- Prove2me | Theorems.Thm_OAI_AlgorithmicThinTrees_MetricProfiles_AssignedGeometry_AssignedSequence_ordered_bound
-- name    : OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedSequence.ordered_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:48:58.341973+00:00
-- url     : https://prove2.me/theorems/25cec577-cc76-47a3-8c6a-477ce5b6c55e
-- title:
--   OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedSequence.ordered_bound: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedSequence.ordered_bound` of [lean/OAI/Combinatorics/ThinTrees/Metric/ScaleCharging.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/ThinTrees/Metric/ScaleCharging.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedSequence`, with `open Finset StrongThinTree StrongThinTree.MultiGraph`, `open AlgorithmicThinTrees.MetricProfiles.CompactGeometry`, `open AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell`, `open scoped Classical`):
--
--   ```lean
--   lemma ordered_bound {J : Type*} [LinearOrder J] (hX : ∀v, isProfile (X v)) (hq : 0 < q)
--       (hconn : LocallyConnectedReal H G q) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
--       (S : Finset J) (F : S → AssignedFamily H G X (6144/q))
--       (hgeo : ∀i j : S, j.val < i.val → (F j).radius ≤ ρ*(F i).radius)
--       (hR : ∀i, (F i).BoundaryRatio ρ)
--       (hdis : ∀i j : S, i≠j → Disjoint (F i).owners (F j).owners) :
--       (q/8192)*(∑i, (F i).mass) ≤ ∑e : Fin m, normDistance (X (G.left e)) (X (G.right e))
--   ```
--
--   **Definitions.** The statement is written with `OAI.AlgorithmicThinTrees.MetricProfiles.Doubled`, `OAI.AlgorithmicThinTrees.MetricProfiles.instPseudoMetricSpaceDoubled`, `OAI.StrongThinTree.MultiGraph.Hierarchy`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedFamily`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.LocallyConnectedReal`, `OAI.AlgorithmicThinTrees.MetricProfiles.CompactGeometry.isProfile`, `OAI.AlgorithmicThinTrees.MetricProfiles.CompactGeometry.normDistance`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedFamily.BoundaryRatio`, `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedFamily.mass` and `OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedFamily.owners` (definitions bundle `OAIQ241TT002` of this split); `OAI.StrongThinTree.MultiGraph` (the published bundle `Def_AlgorithmicThinTrees`).
--
--   **Used by.** The proof of `OAI.AlgorithmicThinTrees.MetricTests.polynomial_nuclear_bound` of this split imports it.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/ThinTrees/Metric/ScaleCharging.lean (declaration OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedSequence.ordered_bound)

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT002

section

attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
open scoped Classical

variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m} {X : Fin n → Doubled Coord → ℝ}

namespace AssignedSequence
variable {η q ρ : ℝ}

lemma ordered_bound {J : Type*} [LinearOrder J] (hX : ∀v, isProfile (X v)) (hq : 0 < q)
    (hconn : LocallyConnectedReal H G q) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (S : Finset J) (F : S → AssignedFamily H G X (6144/q))
    (hgeo : ∀i j : S, j.val < i.val → (F j).radius ≤ ρ*(F i).radius)
    (hR : ∀i, (F i).BoundaryRatio ρ)
    (hdis : ∀i j : S, i≠j → Disjoint (F i).owners (F j).owners) :
    (q/8192)*(∑i, (F i).mass) ≤ ∑e : Fin m, normDistance (X (G.left e)) (X (G.right e)) := by
  sorry
end AssignedSequence
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

end

end OAI
end
