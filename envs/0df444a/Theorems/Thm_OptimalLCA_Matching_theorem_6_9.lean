-- Prove2me | Theorems.Thm_OptimalLCA_Matching_theorem_6_9
-- name    : OptimalLCA.Matching.theorem_6_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:47:58.184066+00:00
-- url     : https://prove2.me/theorems/614b2551-80e1-454a-9d20-573a061ec6e2
-- title:
--   Theorem 6.9 — exact local sampler for q^(δ)_u with expected work and queries A₀^{T_δ+1} = (2Δ)^{O(1/δ)}
-- statement:
--   There are absolute constants $A_0\ge2$ and $c>0$ with $A_0^{T_\delta+1}\le(2\Delta)^{c/\delta}$ for all $\Delta\ge2$, $0<\delta<1$, such that for every $\Delta\ge2$ and $0<\delta<1$ there is a program (the paper's Algorithm 4) with the following property. For every graph $G$ of maximum degree at most $\Delta$, given by adjacency lists, and every vertex $u$, the program run at $u$ returns an exact sample from $q^{(\delta)}_u$ (a neighbour $v$ with probability $q^{(\delta)}_{uv}$, the dummy with probability $q^{(\delta)}_{u\perp}$), where
--   $$(2-\delta)\nu_f(G)\le P(q^{(\delta)})\le2\nu_f(G);$$
--   it terminates almost surely, and its expected total work and expected number of graph queries are at most $C(\delta,\Delta)=A_0^{T_\delta+1}$.
--
--   Differences from the source:
--   - reading: Algorithm 4 returns an exact sample … with expected total work at most C(δ, Δ) := A₀^{T_δ+1} = (2Δ)^{O(1/δ)} → ∃ absolute A₀ ≥ 2 and c > 0 with A₀^{T_δ+1} ≤ (2Δ)^{c/δ}, and for each Δ, δ ∃ a program (independent of G, n and u) with these properties; reason: Algorithm 4's constants are not printed; the statement is about the existence of such a sampler with an absolute A₀
--   - encoding: an exact sample from q^(δ)_u → output v.val with probability q^(δ)_{uv} for each neighbour v, −1 with probability q^(δ)_{u⊥}; reason: the machine's output register; ⊥ encoded as −1
--   - encoding: expected total work / graph queries → outer expectations of the ℕ∞-valued totals under the tape law; reason: non-halting runs count as ∞
--   - encoding: independent invocations use independent randomness → each invocation is one run on its own tape; reason: the statement concerns one invocation
--   - encoding: vertices [n] → Fin n, vertex v as the integer v.val; reason: relabelling
-- source:
--   Cohen, Roghani, Optimal LCA and Sublinear Estimation for Bipartite Matching in Δ^O(1/ε) Queries, arXiv:2611.06024 (version not printed; PDF sha256 5a43ec12…3eb3), p. 38, Theorem 6.9

import Mathlib
import Definitions.Def_OptimalLCA_Matching_Graph
import Definitions.Def_OptimalLCA_Matching_Machine
import Definitions.Def_OptimalLCA_Matching_SaddlePoint
import Definitions.Def_OptimalLCA_Matching_Optimizer

namespace OptimalLCA.Matching

/-- Theorem 6.9 (local proposal sampler), existential reading of "Algorithm 4". There are
absolute constants `A₀ ≥ 2` and `c > 0` with `A₀^{T_δ+1} ≤ (2Δ)^{c/δ}` such that for every
`Δ ≥ 2` and `0 < δ < 1` some program, run at a vertex `u` of any graph of maximum degree at
most `Δ` given by adjacency lists, returns an exact sample from `q^{(δ)}_u` (a neighbour `v`
as `v.val`, the dummy as `-1`), where `(2 - δ) ν_f(G) ≤ P(q^{(δ)}) ≤ 2 ν_f(G)`; it halts
almost surely and its expected total work and expected number of graph queries are at most
`C(δ, Δ) = A₀^{T_δ+1}`. -/
theorem theorem_6_9 :
    ∃ A₀ : ℝ, 2 ≤ A₀ ∧ ∃ c : ℝ, 0 < c ∧
    ∀ Δ : ℕ, 2 ≤ Δ → ∀ δ : ℝ, 0 < δ → δ < 1 →
      A₀ ^ (tDelta Δ δ + 1) ≤ (2 * (Δ : ℝ)) ^ (c / δ) ∧
      ∃ P : Program, ∀ (n : ℕ) (A : AdjLists (Fin n)), A.MaxDegLE Δ → ∀ u : Fin n,
        ((2 - δ) * fracMatchingNumber A.toGraph ≤
            acceptedMass A.toGraph (qDelta A.toGraph Δ δ) ∧
          acceptedMass A.toGraph (qDelta A.toGraph Δ δ) ≤
            2 * fracMatchingNumber A.toGraph) ∧
        tapeMeasure {ω | ¬ Halts P (graphEnv A (tapeReal ω))
            (fun a => if a = 0 then (u.val : ℝ) else 0)} = 0 ∧
        (∀ d : A.toGraph.Dart, d.fst = u →
          tapeMeasure {ω | output P (graphEnv A (tapeReal ω))
              (fun a => if a = 0 then (u.val : ℝ) else 0) = some (d.snd.val : ℝ)} =
            ENNReal.ofReal (qDelta A.toGraph Δ δ (Sum.inr d))) ∧
        tapeMeasure {ω | output P (graphEnv A (tapeReal ω))
            (fun a => if a = 0 then (u.val : ℝ) else 0) = some (-1)} =
          ENNReal.ofReal (qDelta A.toGraph Δ δ (Sum.inl u)) ∧
        outerLIntegral tapeMeasure (fun ω => ENat.toENNReal (workOf P (graphEnv A (tapeReal ω))
            (fun a => if a = 0 then (u.val : ℝ) else 0))) ≤
          ENNReal.ofReal (A₀ ^ (tDelta Δ δ + 1)) ∧
        outerLIntegral tapeMeasure (fun ω => ENat.toENNReal (queriesOf P
            (graphEnv A (tapeReal ω)) (fun a => if a = 0 then (u.val : ℝ) else 0))) ≤
          ENNReal.ofReal (A₀ ^ (tDelta Δ δ + 1)) := by sorry

end OptimalLCA.Matching
