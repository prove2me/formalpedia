-- Prove2me | Theorems.Thm_OAI_BufferedIsing_finite_graph_comparison
-- name    : OAI.BufferedIsing.finite_graph_comparison
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:24.893694+00:00
-- url     : https://prove2.me/theorems/837997cc-0593-4a17-8f60-8bb69bc38401
-- statement:
--   The theorem states a comparison bound for a ferromagnetic Ising model on a finite graph with n vertices and m separately indexed edges (parallel edges allowed, no loops, nonnegative couplings K_e) and an arbitrary real external field h. A configuration σ has energy equal to the sum over edges of K_e σ_u σ_v plus the sum over vertices of h_v σ_v, with spins ±1, and weight exp(energy). Take pairwise disjoint vertex sets I, J, F, and kept vertices i ∈ I and j ∈ J that lie outside F. Fix spin configurations a and τ. For a configuration b, the conditional probability of σ_I = a given σ_J = b and σ_F = τ is the ratio of the total weight of configurations satisfying all three agreements to the total weight of those agreeing with b on J and τ on F. For any two probability mixtures mix and mix' on configurations (nonnegative weights summing to 1), the mixture probability is the mix-weighted average of these conditional probabilities over b; only the restriction of b to J matters. Let q be the terminal connection probability in the zero-field random-cluster (FK) model with q=2 on the graph with F deleted (not pinned): edges e are open with probability 1-exp(-2K_e), the vertices of I are identified together and those of J are identified together, and q is the probability that i and j lie in the same cluster. Then the ratio of the mixture probability under mix to that under mix' lies between exp(-4 artanh q) and exp(4 artanh q), for every such pair of mixtures, uniformly in h, a and τ. The theorem is stated with its proof admitted (sorry).
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/BufferedIsing.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/BufferedIsing.lean; bytes 4276..5101
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_BufferedIsing

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

/-- Finite-graph comparison for arbitrary probability mixtures on both sides.
Dirac mixtures recover the conditional laws. -/
theorem finite_graph_comparison {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIJ : Disjoint I J) (hIF : Disjoint I F) (hJF : Disjoint J F)
    (i j : KeptVertex F) (hi : i.val ∈ I) (hj : j.val ∈ J)
    (a τ : Spins n) (mix mix' : Spins n → ℝ)
    (hmix : ∀ b, 0 ≤ mix b) (hmix' : ∀ b, 0 ≤ mix' b)
    (hmixsum : ∑ b, mix b = 1) (hmix'sum : ∑ b, mix' b = 1) :
    Real.exp (-4 * Real.artanh (qZero G I J F i j)) ≤
        mixtureProb G h I J F a τ mix / mixtureProb G h I J F a τ mix' ∧
      mixtureProb G h I J F a τ mix / mixtureProb G h I J F a τ mix' ≤
        Real.exp (4 * Real.artanh (qZero G I J F i j)) := by
  sorry

end BufferedIsing
end OAI
