-- Prove2me | Theorems.Thm_OMSRArbitrary_lemma_20
-- name    : OMSRArbitrary.lemma_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:38:14.296988+00:00
-- url     : https://prove2.me/theorems/3bd33564-0eed-45b2-becf-fd8e0a533bd9
-- title:
--   Lemma 20 — $\mathbb E[V]$ and $\mathbb E[W]$ are at most $\Pr[\mathrm{PG}(u)\text{ matches }i]$
-- statement:
--   Throughout, $g:[0,1]\to[0,1]$ is continuous and nondecreasing with $g(1)<1$, every resource has a weight $r_i>0$ and every edge a success probability $p_{it}\in(0,1]$. Let the weights lie within a factor $\Lambda\in[1,\infty]$ of each other. Fix a resource $i$ and seeds $u=(u_k)$ in $[0,1]$, write $u=u_i$, and let expectations and probabilities be over the thresholds $z$ of the correlated model.
--
--   **Lemma 20.** The following statements hold.
--
--   1. (A) $\mathbb E[V]\le\Pr[\mathrm{PG}(u)\text{ matches }i]$.
--   2. (B) $\mathbb E[W]\le\Pr[\mathrm{PG}(u)\text{ matches }i]$.
--
--   Together with $M\le(g(u)-c(u))V+c(u)W$ (eq. (9), from Lemma 18) this gives the hypothesis of Lemma 19.
--
--   Differences from the source:
--   - encoding: a finite set U of resources and arrivals t ∈ [T] = {1, …, T} → resources Fin n and arrivals Fin m, 0-based, for every n, m; reason: relabelling; every finite instance, including empty ones, is covered
--   - encoding: edge probabilities p_it ∈ (0,1] and weights r_i > 0 → the published Instance (r ≥ 0, p ∈ [0,1] on edges) with hypotheses 0 < r_k and 0 < p_e for e ∈ E; reason: the same instances
--   - encoding: g : [0,1] → [0,1] continuous and nondecreasing with g(1) < 1 → g : ℝ → ℝ with ContinuousOn, MonotoneOn and MapsTo on [0,1] and g 1 < 1; reason: only the values of g on [0,1] enter, since seeds lie in [0,1]
--   - encoding: ties broken in a fixed order of the resources → ties broken toward the smaller resource index; reason: resources can be relabelled, so every fixed order is the index order of some labelling
--   - encoding: Λ ∈ [1, ∞] and weights within a factor Λ of each other; σ_Λ = σ/Λ → ρ = 1/Λ ∈ [0,1] with ρ r_j ≤ r_k for all j, k; σ_Λ = ρ σ; reason: ρ = 0 is Λ = ∞ and ρ = 1 is Λ = 1
--   - encoding: E and Pr over the thresholds z with all seeds fixed (Sections 4–5, App. F) → integrals over z ∼ seedLaw m (i.i.d. uniform on [0,1]) at a fixed seed vector u ∈ [0,1]^n; reason: the correlated model draws z i.i.d. uniform on [0,1]
-- source:
--   Udwani, Online Matching with Arbitrary Stochastic Rewards, arXiv:2611.03598, Lemma 20, p.25 ((A) proved in App. F.2, pp.41–42; (B) in §5.2, pp.25–28)

import Mathlib
import Definitions.Def_OMSRArbitrary_PerResource

open scoped BigOperators
open MeasureTheory
open StochasticRewardMatching.Decomposable (Instance Seeds seedLaw unitSeeds)
noncomputable section

namespace OMSRArbitrary

/-- **Lemma 20** (arXiv:2611.03598, §5.1, p.25; (A) proved in App. F.2, pp.41–42, (B) in §5.2,
pp.25–28): (A) `E[V] ≤ Pr[PG(u) matches i]`; (B) `E[W] ≤ Pr[PG(u) matches i]`.

Seeds `u` fixed, expectations over the thresholds `z`, weights within a factor `Λ` of each other
(`ρ = 1/Λ`), as in Section 5 (p.23). -/
theorem lemma_20 {n m : ℕ} (D : Instance n m) (hr : ∀ k, 0 < D.reward k)
    (hp : ∀ e ∈ D.edges, 0 < D.probability e)
    (g : ℝ → ℝ) (hg_cont : ContinuousOn g (Set.Icc 0 1)) (hg_mono : MonotoneOn g (Set.Icc 0 1))
    (hg_maps : Set.MapsTo g (Set.Icc 0 1) (Set.Icc 0 1)) (hg_one : g 1 < 1)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρr : ∀ j k, ρ * D.reward j ≤ D.reward k)
    (u : Seeds n) (hu : unitSeeds u) (i : Fin n) :
    ∫ z, Vmax D g ρ u i z ∂seedLaw m ≤ matchProb D g u i ∧
    ∫ z, Wmax D g ρ u i z ∂seedLaw m ≤ matchProb D g u i := by sorry

end OMSRArbitrary
