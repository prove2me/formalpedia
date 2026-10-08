-- Prove2me | Theorems.Thm_OAI_Problem336_fusf_is_factor_iid
-- name    : OAI.Problem336.fusf_is_factor_iid
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:08.846927+00:00
-- url     : https://prove2.me/theorems/6ee05276-1089-4dad-8bb9-39dad44c195f
-- statement:
--   The theorem states that there exists a single edge-selection rule Φ that is Borel measurable, relabeling-equivariant, and valid on every graph. Here a graph is coded as a symmetric, irreflexive adjacency function a : ℕ → ℕ → Bool on vertex set ℕ, an edge is a pair (u,v) of naturals with u<v, and a rule Φ takes a graph G, a vertex labeling U : ℕ → ℝ and an edge e to a Boolean. Borel means that (G,U,e) ↦ Φ(G,U,e) is measurable on the product of the graph space, the label space and the edge space. Equivariant means that for every bijection σ of ℕ, applying σ to the vertices of G, to the labels (the new label at u is U(σ⁻¹ u)) and to the edge e leaves the output unchanged. Φ works on G if, whenever G is connected and locally finite, the following holds for every type Ω with a measurable space structure, every measure P on Ω and every family U_v : Ω → ℝ of measurable functions that is vertex-i.i.d., meaning that for every finite set s of vertices and measurable sets A_i, P{ω : U_i(ω) ∈ A_i for all i ∈ s} equals the product over i ∈ s of the Lebesgue measure of A_i ∩ [0,1]. Then the random edge configuration X(ω)(e) = Φ(G,(U_v(ω))_v,e) has the free uniform spanning forest law: each X(·)(e) is measurable, and for every connected exhaustion (H_n) of G and all finite sets A and B of edges, the proportion of spanning trees of H_n that contain every edge of A and no edge of B tends as n→∞ to P{X(e)=true for all e ∈ A and X(e)=false for all e ∈ B}. A connected exhaustion is a sequence of finite nonempty subgraphs of G, each connected, increasing in both vertices and edges, that eventually contains every edge of G.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/FreeUniformSpanningForest.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/FreeUniformSpanningForest.lean; bytes 4360..4508
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_FreeUniformSpanningForest

namespace OAI

noncomputable section

open MeasureTheory

open scoped BigOperators ENNReal Topology

namespace Problem336

theorem fusf_is_factor_iid :
    ∃ Phi : FactorRule, RuleBorel Phi ∧ RuleEquivariant Phi ∧ ∀ G : GraphCode, WorksOnGraph Phi G := by
  sorry

end Problem336
end
end OAI
