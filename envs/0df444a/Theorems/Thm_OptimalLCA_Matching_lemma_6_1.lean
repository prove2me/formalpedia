-- Prove2me | Theorems.Thm_OptimalLCA_Matching_lemma_6_1
-- name    : OptimalLCA.Matching.lemma_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:48:26.748226+00:00
-- url     : https://prove2.me/theorems/0d516c7b-43cd-4cd1-b91a-eceda354ef94
-- title:
--   Lemma 6.1 — elementary-formula Bernoulli factories with constant expected flips and work
-- statement:
--   Let $\Phi(p_1,\dots,p_k)$ be a fixed finite formula built from input coordinates and real constants with $+,-,\times,\div,\exp,\sqrt{\cdot}$ and fourth roots, and $\beta>0$, $0<\gamma<\tfrac12$ known constants. There is a constant $K$ depending only on $\Phi,\beta,\gamma$ such that for every set $S\subseteq[0,1]^k$ of inputs satisfying (a) every denominator and every root argument of $\Phi$ is at least $\beta$, (b) $\Phi(p)\in[\gamma,1-\gamma]$, there is a factory program which, given independent coins of biases $p\in S$, is an exact $\Phi(p)$-coin:
--   $$\Pr[\text{halts}]=1,\quad\Pr[\text{output}=1]=\Phi(p),\quad\Pr[\text{output}=0]=1-\Phi(p),$$
--   with expected number of input flips and expected additional work at most $K$, uniformly over $p\in S$.
--
--   Differences from the source:
--   - encoding: independent coins of biases p₁, …, p_k → flip k returns 1[c_{k,m} < p_k] for i.i.d. uniform c_{k,m}, read only through the flip instruction; reason: successive flips are independent Bern(p_k) bits; the program never sees p
--   - encoding: exact Φ(p)-coin that terminates almost surely → halting set of full measure, P(output 1) = Φ(p), P(output 0) = 1 − Φ(p) (outer measures); reason: definition of an exact coin
--   - encoding: expected number of input flips and expected additional work → outer expectations of the ℕ∞-valued totals (∞ on non-halting runs); additional work = executed instructions other than flips; reason: non-halting runs are not truncated
--   - encoding: fourth root → x^(1/4) (Real.rpow); reason: the root argument is ≥ β > 0 by (a)
-- source:
--   Cohen, Roghani, Optimal LCA and Sublinear Estimation for Bipartite Matching in Δ^O(1/ε) Queries, arXiv:2611.06024 (version not printed; PDF sha256 5a43ec12…3eb3), p. 30, Lemma 6.1

import Mathlib
import Definitions.Def_OptimalLCA_Matching_Machine
import Definitions.Def_OptimalLCA_Matching_Factory

namespace OptimalLCA.Matching

/-- Lemma 6.1 (elementary-formula factories). Let `Φ` be a fixed elementary formula in
`k` inputs and `β > 0`, `0 < γ < 1/2` known constants. There is a constant `K` depending
only on `Φ, β, γ` such that for every set `S ⊆ [0, 1]^k` of inputs at which every
denominator and root argument of `Φ` is at least `β` and `Φ(p) ∈ [γ, 1 - γ]`, some factory
program that sees the biases only through input-coin flips is, for every `p ∈ S`, an exact
`Φ(p)`-coin that halts almost surely, with expected number of input flips and expected
additional work at most `K`. -/
theorem lemma_6_1 (k : ℕ) (Φ : Formula k) (β γ : ℝ) (hβ : 0 < β) (hγ : 0 < γ)
    (hγ' : γ < 1 / 2) :
    ∃ K : ℝ, ∀ S : Set (Fin k → ℝ),
      (∀ p ∈ S, ∀ i, p i ∈ Set.Icc (0 : ℝ) 1) →
      (∀ p ∈ S, Φ.Valid β p ∧ Φ.eval p ∈ Set.Icc γ (1 - γ)) →
      ∃ F : Program, ∀ p ∈ S,
        factoryMeasure {w | ¬ Halts F (factoryEnv p w.1 w.2) (fun _ => 0)} = 0 ∧
        factoryMeasure {w | output F (factoryEnv p w.1 w.2) (fun _ => 0) = some 1} =
          ENNReal.ofReal (Φ.eval p) ∧
        factoryMeasure {w | output F (factoryEnv p w.1 w.2) (fun _ => 0) = some 0} =
          ENNReal.ofReal (1 - Φ.eval p) ∧
        outerLIntegral factoryMeasure
            (fun w => ENat.toENNReal (flipsOf F (factoryEnv p w.1 w.2) (fun _ => 0))) ≤
          ENNReal.ofReal K ∧
        outerLIntegral factoryMeasure
            (fun w => ENat.toENNReal (addlWorkOf F (factoryEnv p w.1 w.2) (fun _ => 0))) ≤
          ENNReal.ofReal K := by sorry

end OptimalLCA.Matching
