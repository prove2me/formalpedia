-- Prove2me | Theorems.Thm_OMSRArbitrary_theorem_4
-- name    : OMSRArbitrary.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:36:20.269519+00:00
-- url     : https://prove2.me/theorems/5a0f84c3-d55c-46ee-a1df-3816fb858971
-- title:
--   Theorem 4 — Perturbed Greedy is $\alpha_\Lambda(g,c)$-competitive against the adaptive offline benchmark, and $\alpha_\infty(g,c)$-competitive for arbitrary weights
-- statement:
--   In **vertex-weighted online matching with stochastic rewards** (OMSR) there are finitely many resources $i$ with weights $r_i>0$ and arrivals $t=1,\dots,T$; each edge $(i,t)$ has a success probability $p_{it}\in(0,1]$. A probe of $(i,t)$ succeeds independently with probability $p_{it}$; a success yields $r_i$ and consumes $i$. **Perturbed Greedy** with perturbation function $g$ draws seeds $u_i\sim U[0,1]$ and probes, at each arrival, the available neighbour with the largest $r_ip_{it}(1-g(u_i))$, ties broken in a fixed order. The **adaptive offline benchmark** $\mathbb E[\mathrm{OPT}]$ is the expected reward of an optimal non-anticipative policy that may probe the edges in any order.
--
--   **Theorem 4.** Let $\Lambda\in[1,\infty]$. For every $c$ with $0\le c\le g$, Perturbed Greedy with perturbation function $g$ is at least $\alpha_\Lambda(g,c)$-competitive against the adaptive offline benchmark for vertex-weighted OMSR on instances whose weights lie within a factor $\Lambda$ of each other. In particular, it is at least $\alpha_\infty(g,c)$-competitive for arbitrary weights.
--
--   Precisely, for every continuous nondecreasing $g:[0,1]\to[0,1]$ with $g(1)<1$, every integrable $c$ with $0\le c\le g$ and every instance:
--
--   1. if $r_j\le\Lambda r_k$ for all resources $j,k$, then
--   $$\alpha_\Lambda(g,c)\cdot\mathbb E[\mathrm{OPT}]\ \le\ \mathbb E[\mathrm{PG}];$$
--   2. without any condition on the weights,
--   $$\alpha_\infty(g,c)\cdot\mathbb E[\mathrm{OPT}]\ \le\ \mathbb E[\mathrm{PG}].$$
--
--   For $\Lambda=1$ and $c\equiv0$ the guarantee is $\alpha(g)$ of Theorem 3.
--
--   **Formalization Note** $\Lambda$ is written $\rho=1/\Lambda\in[0,1]$. $\mathbb E[\mathrm{OPT}]$ is the published `benchmark D false`, a supremum over randomized history-dependent policies with no ordering restriction; $\mathbb E[\mathrm{PG}]$ is computed in the independent model.
--
--   Differences from the source:
--   - encoding: a finite set U of resources and arrivals t ∈ [T] = {1, …, T} → resources Fin n and arrivals Fin m, 0-based, for every n, m; reason: relabelling; every finite instance, including empty ones, is covered
--   - encoding: edge probabilities p_it ∈ (0,1] and weights r_i > 0 → the published Instance (r ≥ 0, p ∈ [0,1] on edges) with hypotheses 0 < r_k and 0 < p_e for e ∈ E; reason: the same instances
--   - encoding: g : [0,1] → [0,1] continuous and nondecreasing with g(1) < 1 → g : ℝ → ℝ with ContinuousOn, MonotoneOn and MapsTo on [0,1] and g 1 < 1; reason: only the values of g on [0,1] enter, since seeds lie in [0,1]
--   - encoding: ties broken in a fixed order of the resources → ties broken toward the smaller resource index; reason: resources can be relabelled, so every fixed order is the index order of some labelling
--   - encoding: Λ ∈ [1, ∞] and weights within a factor Λ of each other; σ_Λ = σ/Λ → ρ = 1/Λ ∈ [0,1] with ρ r_j ≤ r_k for all j, k; σ_Λ = ρ σ; reason: ρ = 0 is Λ = ∞ and ρ = 1 is Λ = 1
--   - encoding: an integrable tradeoff function c : [0,1] → [0,1] with 0 ≤ c ≤ g → c : ℝ → ℝ, IntegrableOn c [0,1], 0 ≤ c x ≤ g x for x ∈ [0,1]; reason: c ≤ g ≤ 1 gives values in [0,1]; values outside [0,1] never enter
--   - encoding: E[OPT], the adaptive offline benchmark (optimal non-anticipative policy, no ordering restriction) → the published benchmark D false: the supremum of the expected reward over randomized history-dependent policies with no ordering restriction; reason: it is the same value: an illegal action only stops the policy, and the extra action (t, none) can be replaced by never probing t
--   - encoding: E[PG] in the standard (independent) model with seeds u_i ∼ U[0,1] → pgValue: the published edgeAverage over independent edge outcomes of the seedAverage over u ∼ U[0,1]^n; reason: direct transcription
--   - encoding: min over y ∈ [0,1] in (4) and (5) → infimum over the subtype [0,1]; reason: the minimum is attained, so it equals the infimum
-- source:
--   Udwani, Online Matching with Arbitrary Stochastic Rewards, arXiv:2611.03598, Theorem 4, p.13 (proof p.25)

import Mathlib
import Definitions.Def_StochasticRewardMatching_Decomposable_Benchmarks
import Definitions.Def_OMSRArbitrary_Guarantees
import Definitions.Def_OMSRArbitrary_PerturbedGreedy

open scoped BigOperators
open MeasureTheory
open StochasticRewardMatching.Decomposable (Instance benchmark)
noncomputable section

namespace OMSRArbitrary

/-- **Theorem 4** (arXiv:2611.03598, §3, p.13): let `Λ ∈ [1, ∞]`. For every `c` with `0 ≤ c ≤ g`,
Perturbed Greedy with perturbation function `g` is at least `α_Λ(g, c)`-competitive against the
adaptive offline benchmark for vertex-weighted OMSR on instances whose weights lie within a
factor `Λ` of each other. In particular, it is at least `α_∞(g, c)`-competitive for arbitrary
weights.

For every instance (resources `Fin n`, arrivals `Fin m`, weights `r_i > 0`, edge probabilities in
`(0,1]`), every continuous nondecreasing `g : [0,1] → [0,1]` with `g(1) < 1` and every
integrable `c` with `0 ≤ c ≤ g` on `[0,1]`:
1. for every `ρ = 1/Λ ∈ [0,1]` with `r_j ≤ Λ r_k` for all `j, k`:
   `α_Λ(g, c) · E[OPT] ≤ E[PG]`;
2. `α_∞(g, c) · E[OPT] ≤ E[PG]` (no hypothesis on the weights).

`E[PG]` is the expected reward of PG in the independent model with seeds `u ∼ U[0,1]^n`;
`E[OPT]` is the published `benchmark D false`, the supremum of the expected reward of all
randomized non-anticipative policies with no ordering restriction (the adaptive offline
benchmark). -/
theorem theorem_4 {n m : ℕ} (D : Instance n m) (hr : ∀ k, 0 < D.reward k)
    (hp : ∀ e ∈ D.edges, 0 < D.probability e)
    (g : ℝ → ℝ) (hg_cont : ContinuousOn g (Set.Icc 0 1)) (hg_mono : MonotoneOn g (Set.Icc 0 1))
    (hg_maps : Set.MapsTo g (Set.Icc 0 1) (Set.Icc 0 1)) (hg_one : g 1 < 1)
    (c : ℝ → ℝ) (hc_int : IntegrableOn c (Set.Icc 0 1))
    (hc_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ c x) (hc_le : ∀ x ∈ Set.Icc (0 : ℝ) 1, c x ≤ g x) :
    (∀ ρ ∈ Set.Icc (0 : ℝ) 1, (∀ j k, ρ * D.reward j ≤ D.reward k) →
      alphaW g c ρ * benchmark D false ≤ pgValue D g) ∧
    alphaInf g c * benchmark D false ≤ pgValue D g := by sorry

end OMSRArbitrary
