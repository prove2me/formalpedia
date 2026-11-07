-- Prove2me | Theorems.Thm_OMSRArbitrary_lemma_5
-- name    : OMSRArbitrary.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:39:11.50821+00:00
-- url     : https://prove2.me/theorems/c96c0785-f8c7-4317-9c2b-0975e50628b0
-- title:
--   Lemma 5 — the dual certificate: (6) for every resource gives $\mathbb E[\mathrm{PG}]\ge\alpha\,\mathbb E[\mathrm{OPT}]$
-- statement:
--   Throughout, $g:[0,1]\to[0,1]$ is continuous and nondecreasing with $g(1)<1$, every resource has a weight $r_i>0$ and every edge a success probability $p_{it}\in(0,1]$.
--   Work in the correlated model with seeds $u_k$ i.i.d. uniform on $[0,1]$. Let $\lambda_t,\theta_i$ be the candidate duals of PG and $O_i$ the arrivals at which OPT probes $i$.
--
--   **Lemma 5.** If for every resource $i$
--   $$\mathbb E\Big[\sum_{t\in O_i}\lambda_t\Big]+\mathbb E[\theta_i]\ \ge\ \alpha\,r_i\Pr[\mathrm{OPT}\text{ matches }i],\tag{6}$$
--   then $\mathbb E[\mathrm{PG}]\ge\alpha\,\mathbb E[\mathrm{OPT}]$.
--
--   The certificate reduces the competitive ratio to one inequality per resource.
--
--   **Formalization Note** The statement is made for every deterministic policy in the role of OPT, with $\mathbb E[\mathrm{OPT}]$ its expected reward; expectations are over $u$ and $z$.
--
--   Differences from the source:
--   - encoding: a finite set U of resources and arrivals t ∈ [T] = {1, …, T} → resources Fin n and arrivals Fin m, 0-based, for every n, m; reason: relabelling; every finite instance, including empty ones, is covered
--   - encoding: edge probabilities p_it ∈ (0,1] and weights r_i > 0 → the published Instance (r ≥ 0, p ∈ [0,1] on edges) with hypotheses 0 < r_k and 0 < p_e for e ∈ E; reason: the same instances
--   - encoding: g : [0,1] → [0,1] continuous and nondecreasing with g(1) < 1 → g : ℝ → ℝ with ContinuousOn, MonotoneOn and MapsTo on [0,1] and g 1 < 1; reason: only the values of g on [0,1] enter, since seeds lie in [0,1]
--   - encoding: ties broken in a fixed order of the resources → ties broken toward the smaller resource index; reason: resources can be relabelled, so every fixed order is the index order of some labelling
--   - generalization: OPT, an optimal non-anticipative policy, taken deterministic → every deterministic policy opt (run through the published legalize D false); reason: the argument uses only that OPT is a legal deterministic non-anticipative policy; the statement specializes to OPT
--   - encoding: E over the seeds and thresholds; E[PG], E[OPT] in the correlated model → iterated integrals over u ∼ seedLaw n and z ∼ seedLaw m; pgValueCorr and optValueCorr; reason: seeds and thresholds are independent uniforms (pp.11, 13)
-- source:
--   Udwani, Online Matching with Arbitrary Stochastic Rewards, arXiv:2611.03598, Lemma 5, eq. (6), p.14

import Mathlib
import Definitions.Def_OMSRArbitrary_Duals

open scoped BigOperators
open MeasureTheory
open StochasticRewardMatching.Decomposable (Instance Seeds seedLaw DetPolicy)
noncomputable section

namespace OMSRArbitrary

open Classical in
/-- **Lemma 5** (arXiv:2611.03598, §3.1, p.14), the dual certificate: if for every resource `i`
`E[∑_{t∈O_i} λ_t] + E[θ_i] ≥ α r_i Pr[OPT matches i]` (6), then `E[PG] ≥ α E[OPT]`.

The expectations are over the seeds `u ∼ seedLaw n` and the thresholds `z ∼ seedLaw m` of the
correlated model; `O_i` is the set of arrivals at which the policy `opt` probes `i`.

**Formalization Note.** OPT is taken deterministic (p.11); the statement is made for every
deterministic policy `opt` in its role. -/
theorem lemma_5 {n m : ℕ} (D : Instance n m) (hr : ∀ k, 0 < D.reward k)
    (hp : ∀ e ∈ D.edges, 0 < D.probability e)
    (g : ℝ → ℝ) (hg_cont : ContinuousOn g (Set.Icc 0 1)) (hg_mono : MonotoneOn g (Set.Icc 0 1))
    (hg_maps : Set.MapsTo g (Set.Icc 0 1) (Set.Icc 0 1)) (hg_one : g 1 < 1)
    (opt : DetPolicy n m) (α : ℝ)
    (h6 : ∀ i : Fin n,
      α * D.reward i * ∫ z, (if optMatches D opt z i then (1 : ℝ) else 0) ∂seedLaw m ≤
        (∫ u, (∫ z, (∑ t ∈ optProbeSet D opt z i, lam D g u z t) ∂seedLaw m) ∂seedLaw n) +
          ∫ u, (∫ z, theta D g u z i ∂seedLaw m) ∂seedLaw n) :
    α * optValueCorr D opt ≤ pgValueCorr D g := by sorry

end OMSRArbitrary
