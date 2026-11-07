-- Prove2me | Theorems.Thm_OMSRArbitrary_lemma_F_1
-- name    : OMSRArbitrary.lemma_F_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:39:18.009314+00:00
-- url     : https://prove2.me/theorems/7897c080-325c-48dd-abb6-3a18783aaa76
-- title:
--   Lemma F.1 — $\mathbb E[\sum_{t\in O_i}\lambda_t]=r_i\,\mathbb E[\sum_{t\in O_i}\mathbf 1\{z_t\le p_{it}\}(\pi_t+e_t)]$
-- statement:
--   Throughout, $g:[0,1]\to[0,1]$ is continuous and nondecreasing with $g(1)<1$, every resource has a weight $r_i>0$ and every edge a success probability $p_{it}\in(0,1]$. Fix a resource $i$ and seeds $u=(u_k)$ in $[0,1]$, write $u=u_i$, and let expectations and probabilities be over the thresholds $z$ of the correlated model. Let OPT be a deterministic non-anticipative policy and $O_i$ the arrivals at which it probes $i$.
--
--   **Lemma F.1 (Weighted form of Lemma 9).**
--   $$\mathbb E\Big[\sum_{t\in O_i}\lambda_t\Big]=r_i\,\mathbb E\Big[\sum_{t\in O_i}\mathbf 1\{z_t\le p_{it}\}(\pi_t+e_t)\Big].$$
--
--   So $\lambda_t$ pays, in expectation, the normalized reduced price $\pi_t$ of PG$^{-i}$ plus the boost at every arrival where OPT probes $i$.
--
--   **Formalization Note** OPT is any deterministic policy.
--
--   Differences from the source:
--   - encoding: a finite set U of resources and arrivals t ∈ [T] = {1, …, T} → resources Fin n and arrivals Fin m, 0-based, for every n, m; reason: relabelling; every finite instance, including empty ones, is covered
--   - encoding: edge probabilities p_it ∈ (0,1] and weights r_i > 0 → the published Instance (r ≥ 0, p ∈ [0,1] on edges) with hypotheses 0 < r_k and 0 < p_e for e ∈ E; reason: the same instances
--   - encoding: g : [0,1] → [0,1] continuous and nondecreasing with g(1) < 1 → g : ℝ → ℝ with ContinuousOn, MonotoneOn and MapsTo on [0,1] and g 1 < 1; reason: only the values of g on [0,1] enter, since seeds lie in [0,1]
--   - encoding: ties broken in a fixed order of the resources → ties broken toward the smaller resource index; reason: resources can be relabelled, so every fixed order is the index order of some labelling
--   - encoding: E and Pr over the thresholds z with all seeds fixed (Sections 4–5, App. F) → integrals over z ∼ seedLaw m (i.i.d. uniform on [0,1]) at a fixed seed vector u ∈ [0,1]^n; reason: the correlated model draws z i.i.d. uniform on [0,1]
--   - generalization: OPT, an optimal non-anticipative policy, taken deterministic → every deterministic policy opt (run through the published legalize D false); reason: the argument uses only that OPT is a legal deterministic non-anticipative policy; the statement specializes to OPT
--   - generalization: standing assumption of App. F that all weights lie within a factor Λ → no hypothesis on weight ratios; reason: the statement does not involve Λ; adding the hypothesis gives the source statement
-- source:
--   Udwani, Online Matching with Arbitrary Stochastic Rewards, arXiv:2611.03598, Lemma F.1, p.39

import Mathlib
import Definitions.Def_OMSRArbitrary_Duals
import Definitions.Def_OMSRArbitrary_PerResource

open scoped BigOperators
open MeasureTheory
open StochasticRewardMatching.Decomposable (Instance Seeds seedLaw DetPolicy unitSeeds)
noncomputable section

namespace OMSRArbitrary

/-- **Lemma F.1** (Weighted Form of Lemma 9; arXiv:2611.03598, App. F, p.39), seeds `u` fixed,
expectations over the thresholds `z`:
`E[∑_{t∈O_i} λ_t] = r_i E[∑_{t∈O_i} 1{z_t ≤ p_{it}}(π_t + e_t)]`.

**Formalization Note.** OPT is any deterministic policy `opt`; `O_i = optProbeSet D opt z i`. -/
theorem lemma_F_1 {n m : ℕ} (D : Instance n m) (hr : ∀ k, 0 < D.reward k)
    (hp : ∀ e ∈ D.edges, 0 < D.probability e)
    (g : ℝ → ℝ) (hg_cont : ContinuousOn g (Set.Icc 0 1)) (hg_mono : MonotoneOn g (Set.Icc 0 1))
    (hg_maps : Set.MapsTo g (Set.Icc 0 1) (Set.Icc 0 1)) (hg_one : g 1 < 1)
    (u : Seeds n) (hu : unitSeeds u) (i : Fin n) (opt : DetPolicy n m) :
    ∫ z, (∑ t ∈ optProbeSet D opt z i, lam D g u z t) ∂seedLaw m =
      D.reward i * ∫ z, (∑ t ∈ optProbeSet D opt z i,
        (if z t ≤ D.probability (i, t) then piW D g u i z t + boost D g u i z t else 0))
        ∂seedLaw m := by sorry

end OMSRArbitrary
