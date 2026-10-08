-- Prove2me | Theorems.Thm_OAI_HoneycombForce_logPartition_tendsto
-- name    : OAI.HoneycombForce.logPartition_tendsto
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:45.541269+00:00
-- url     : https://prove2.me/theorems/5d99d8ab-1666-46f6-8fb4-087223a42563
-- statement:
--   The theorem states that, for every starting vertex o of the honeycomb lattice, every complex number e and every real number s, the sequence logPartition(o,e,s)(n) converges as n tends to infinity to freeEnergy(o,e,s). Here vertices are triangular-up or triangular-down sites labeled by integer column and row, each up vertex being adjacent to three down vertices and vice versa, with planar positions given in the complex plane. saws(o,n) is the set of self-avoiding walks of n steps from o, meaning vertex lists with no repetition. For such a walk γ, its displacement is the position of its endpoint minus the position of o, and its projection onto e is the real part of conj(e) times the displacement. The partition function is the sum over γ in saws(o,n) of ρ^n exp(s times that projection), with ρ = 1/√(2+√2). logPartition is log of this partition function divided by n, and freeEnergy is defined as the limit of logPartition at infinity, using Lean's limUnder convention. The statement therefore asserts that this limit exists and equals freeEnergy; it is a stated theorem whose proof is admitted in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/HoneycombFreeEnergy.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/HoneycombFreeEnergy.lean; bytes 1750..1892
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_HoneycombFreeEnergy

namespace OAI

noncomputable section

open scoped ENNReal Topology

open Filter

namespace HoneycombForce

theorem logPartition_tendsto (o : Vertex) (e : ℂ) (s : ℝ) :
    Tendsto (logPartition o e s) atTop (𝓝 (freeEnergy o e s)) := by
  sorry

end HoneycombForce
end
end OAI
