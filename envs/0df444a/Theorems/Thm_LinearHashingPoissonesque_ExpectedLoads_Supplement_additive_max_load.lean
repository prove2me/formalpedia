-- Prove2me | Theorems.Thm_LinearHashingPoissonesque_ExpectedLoads_Supplement_additive_max_load
-- name    : LinearHashingPoissonesque.ExpectedLoads.Supplement.additive_max_load
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:07:50.431601+00:00
-- url     : https://prove2.me/theorems/a319b0e9-c260-4724-9f1c-6ef99d7970ac
-- title:
--   Theorem 2 (companion theorem; not used in the proof of the goal) — additive maximum-load comparison
-- statement:
--   There are real sequences $c_\ell,e_\ell$ with $0\le c_\ell<1$ and $e_\ell\to0$, chosen uniformly in the ambient dimension and the input set, such that for every $u\ge\ell\ge1$, $n=2^\ell$, and $S\subseteq\mathbb F_2^u$ of cardinality $n$, a uniformly random linear $h:\mathbb F_2^u\to\mathbb F_2^\ell$ satisfies
--
--   $$\mathbb E_h\!\left[\max_{y\in\mathbb F_2^\ell}|h^{-1}(y)\cap S|\right]
--   \le R(n,n)+\tfrac12+c_\ell+e_\ell.$$
--
--   Moreover, for the same sequence $c$, there is a strictly increasing sequence of indices $\ell_j$ with
--
--   $$c_{\ell_j}\longrightarrow0.$$
--
--   Here $R(n,n)$ is the expected maximum load of a fully random map $[n]\to[n]$. The theorem retains the oscillatory additive term and its vanishing subsequence, rather than replacing it with a larger constant.
--
--   Differences from the source:
--   - encoding: binary coordinate spaces and n = 2^ℓ → Fin u → ZMod 2 and Fin ℓ → ZMod 2, with n substituted as 2^ell; reason: these are exactly the source spaces and their cardinalities; ell is independent of the number of balls
--   - encoding: averages of the heaviest and lightest r labelled bins → published heaviestAverage and lightestAverage; reason: sorting all bin loads preserves every empty bin and every multiplicity
--   - encoding: uniform linear expectation and a fully random comparison expectation → published avgLin and fullyRandomMaxLoad n n; reason: both are the exact finite uniform laws, with all bins counted
--   - encoding: c_ell and o_ell(1), and an increasing subsequence for the same c → ∃ c e before ell,u,S, Tendsto e to zero and ∃ strictly monotone phi with Tendsto (c ∘ phi) to zero; reason: the error is uniform in u and S and both clauses use the same c; the unused values at ell=0 can be chosen arbitrarily
-- source:
--   Vinayak Kumar, STOC 2027 submission #1155 (October 2026), p.4, Theorem 2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1155.pdf#page=4

import Definitions.Def_LinMaxLoad_avgLin
import Definitions.Def_LinearHashingPoissonesque_ExpectedLoads_Supplement_FullyRandomMaxLoad

namespace LinearHashingPoissonesque.ExpectedLoads.Supplement

open Filter Topology in
/-- Theorem 2, p.4 (proof pp.17–18): the same c works in both conclusions;
c and the null error are chosen uniformly in u and S. -/
theorem additive_max_load :
    ∃ c e : ℕ → ℝ,
      (∀ ell : ℕ, 0 ≤ c ell ∧ c ell < 1) ∧
      Tendsto e atTop (𝓝 0) ∧
      (∀ ell u : ℕ, 1 ≤ ell → ell ≤ u →
        ∀ S : Finset (Fin u → ZMod 2), S.card = 2 ^ ell →
          LinMaxLoad.avgLin (ZMod 2) (Fin u → ZMod 2) ell
              (fun h => heaviestAverage S h 1) ≤
            fullyRandomMaxLoad (2 ^ ell) (2 ^ ell) + (1 : ℝ) / 2 + c ell + e ell) ∧
      ∃ phi : ℕ → ℕ, StrictMono phi ∧ Tendsto (c ∘ phi) atTop (𝓝 0) := by sorry

end LinearHashingPoissonesque.ExpectedLoads.Supplement
