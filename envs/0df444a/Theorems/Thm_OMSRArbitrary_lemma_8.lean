-- Prove2me | Theorems.Thm_OMSRArbitrary_lemma_8
-- name    : OMSRArbitrary.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:38:17.126463+00:00
-- url     : https://prove2.me/theorems/6fc147ea-19b5-455d-a125-810849c2dab0
-- title:
--   Lemma 8 — adding $i$ only enlarges the available sets; $P_t\ge P_t^{-i}$ and $e_t\ge0$
-- statement:
--   Throughout, $g:[0,1]\to[0,1]$ is continuous and nondecreasing with $g(1)<1$, every resource has a weight $r_i>0$ and every edge a success probability $p_{it}\in(0,1]$. Fix a resource $i$ and seeds $u=(u_k)$ in $[0,1]$, write $u=u_i$, and let expectations and probabilities be over the thresholds $z$ of the correlated model.
--
--   **Lemma 8.** Pathwise, at every arrival $t$, the set of resources available in PG$(u)$ at $t$ contains the set available in PG$^{-i}$ at $t$. Consequently $P_t\ge P_t^{-i}$ and $e_t\ge0$ for all $t$.
--
--   Here $P_t$, $P_t^{-i}$ are the reduced prices of the probes of PG$(u)$ and PG$^{-i}$ at $t$ ($0$ if none) and $e_t=(P_t-P_t^{-i})/(r_ip_{it})$ for $(i,t)\in E$. The boost $e_t\ge0$ is the known lower bound on $\lambda_t$ that the analysis starts from.
--
--   Differences from the source:
--   - encoding: a finite set U of resources and arrivals t ∈ [T] = {1, …, T} → resources Fin n and arrivals Fin m, 0-based, for every n, m; reason: relabelling; every finite instance, including empty ones, is covered
--   - encoding: edge probabilities p_it ∈ (0,1] and weights r_i > 0 → the published Instance (r ≥ 0, p ∈ [0,1] on edges) with hypotheses 0 < r_k and 0 < p_e for e ∈ E; reason: the same instances
--   - encoding: g : [0,1] → [0,1] continuous and nondecreasing with g(1) < 1 → g : ℝ → ℝ with ContinuousOn, MonotoneOn and MapsTo on [0,1] and g 1 < 1; reason: only the values of g on [0,1] enter, since seeds lie in [0,1]
--   - encoding: ties broken in a fixed order of the resources → ties broken toward the smaller resource index; reason: resources can be relabelled, so every fixed order is the index order of some labelling
--   - generalization: pathwise, for sample paths (thresholds z ∈ [0,1]^m) → for every z ∈ ℝ^m; reason: the claim holds verbatim for every threshold vector; restricting z to [0,1]^m gives the source statement
--   - encoding: the set available at arrival t; P_t^{−i} = 0 if PG^{−i} probes nothing; e_t for (i, t) ∈ E → pgAvail just before arrival t; pgPrice = 0 without a probe; boost at edges (i, t); reason: the source conventions (pp.15, 39)
-- source:
--   Udwani, Online Matching with Arbitrary Stochastic Rewards, arXiv:2611.03598, Lemma 8, p.16 (proof p.38; holds verbatim with weights, p.39)

import Mathlib
import Definitions.Def_OMSRArbitrary_PerResource

open scoped BigOperators
open MeasureTheory
open StochasticRewardMatching.Decomposable (Instance Seeds unitSeeds)
noncomputable section

namespace OMSRArbitrary

/-- **Lemma 8** (arXiv:2611.03598, §4, p.16; proof p.38; holds verbatim with weights, p.39):
pathwise, at every arrival `t`, the set of resources available in PG(u) at `t` contains the set
available in PG^{−i} at `t`. Consequently `P_t ≥ P_t^{−i}` and `e_t ≥ 0` for all `t`.

PG(u) is the run from all resources, PG^{−i} the run from `univ.erase i` with the same seeds and
thresholds `z`; `e_t = (P_t − P_t^{−i})/(r_i p_{it})` is defined at arrivals with an edge to `i`. -/
theorem lemma_8 {n m : ℕ} (D : Instance n m) (hr : ∀ k, 0 < D.reward k)
    (hp : ∀ e ∈ D.edges, 0 < D.probability e)
    (g : ℝ → ℝ) (hg_cont : ContinuousOn g (Set.Icc 0 1)) (hg_mono : MonotoneOn g (Set.Icc 0 1))
    (hg_maps : Set.MapsTo g (Set.Icc 0 1) (Set.Icc 0 1)) (hg_one : g 1 < 1)
    (u : Seeds n) (hu : unitSeeds u) (i : Fin n) (z : Seeds m) :
    (∀ t : Fin m, pgAvail D g u (Finset.univ.erase i) 0 (corrOutcome D z) t.val ⊆
      pgAvail D g u Finset.univ 0 (corrOutcome D z) t.val) ∧
    (∀ t : Fin m, pgPrice D g u (Finset.univ.erase i) 0 (corrOutcome D z) t ≤
      pgPrice D g u Finset.univ 0 (corrOutcome D z) t) ∧
    (∀ t : Fin m, (i, t) ∈ D.edges → 0 ≤ boost D g u i z t) := by sorry

end OMSRArbitrary
