-- Prove2me | Theorems.Thm_OMSRArbitrary_lemma_18
-- name    : OMSRArbitrary.lemma_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:38:12.000629+00:00
-- url     : https://prove2.me/theorems/252d1113-26d3-476b-96ae-cf93590eaaf0
-- title:
--   Lemma 18 — demand bounds: (A), (B), and $D_t\le(g(u)-c(u))v_t(u)+c(u)w_t(u)$
-- statement:
--   Throughout, $g:[0,1]\to[0,1]$ is continuous and nondecreasing with $g(1)<1$, every resource has a weight $r_i>0$ and every edge a success probability $p_{it}\in(0,1]$. Let the weights lie within a factor $\Lambda\in[1,\infty]$ of each other and $c$ be integrable with $0\le c\le g$. Fix a resource $i$ and seeds $u=(u_k)$ in $[0,1]$, write $u=u_i$, and let expectations and probabilities be over the thresholds $z$ of the correlated model.
--
--   **Lemma 18.** Pathwise, for every $t$ with $(i,t)\in E$ and $\delta_t(u)>0$:
--
--   1. (A) $D_t\le g(u)-c(u)+c(u)\,w_t(u)$;
--   2. (B) if PG$(u)$ probes at $t$ a resource whose reduced price is at least $r_ip_{it}(1-g(u))$, then $e_t\ge\delta_t(u)$ and $D_t\le(g(u)-c(u))\sigma_\Lambda(u)+c(u)\,w_t(u)$.
--
--   Overall, $D_t\le(g(u)-c(u))\,v_t(u)+c(u)\,w_t(u)$.
--
--   This splits the demand into the two parts $V$ and $W$ that Lemma 20 pays for.
--
--   Differences from the source:
--   - encoding: a finite set U of resources and arrivals t ∈ [T] = {1, …, T} → resources Fin n and arrivals Fin m, 0-based, for every n, m; reason: relabelling; every finite instance, including empty ones, is covered
--   - encoding: edge probabilities p_it ∈ (0,1] and weights r_i > 0 → the published Instance (r ≥ 0, p ∈ [0,1] on edges) with hypotheses 0 < r_k and 0 < p_e for e ∈ E; reason: the same instances
--   - encoding: g : [0,1] → [0,1] continuous and nondecreasing with g(1) < 1 → g : ℝ → ℝ with ContinuousOn, MonotoneOn and MapsTo on [0,1] and g 1 < 1; reason: only the values of g on [0,1] enter, since seeds lie in [0,1]
--   - encoding: ties broken in a fixed order of the resources → ties broken toward the smaller resource index; reason: resources can be relabelled, so every fixed order is the index order of some labelling
--   - encoding: Λ ∈ [1, ∞] and weights within a factor Λ of each other; σ_Λ = σ/Λ → ρ = 1/Λ ∈ [0,1] with ρ r_j ≤ r_k for all j, k; σ_Λ = ρ σ; reason: ρ = 0 is Λ = ∞ and ρ = 1 is Λ = 1
--   - encoding: an integrable tradeoff function c : [0,1] → [0,1] with 0 ≤ c ≤ g → c : ℝ → ℝ, IntegrableOn c [0,1], 0 ≤ c x ≤ g x for x ∈ [0,1]; reason: c ≤ g ≤ 1 gives values in [0,1]; values outside [0,1] never enter
--   - generalization: pathwise, for sample paths (thresholds z ∈ [0,1]^m) → for every z ∈ ℝ^m; reason: the claim holds verbatim for every threshold vector; restricting z to [0,1]^m gives the source statement
-- source:
--   Udwani, Online Matching with Arbitrary Stochastic Rewards, arXiv:2611.03598, Lemma 18, p.24 (restated p.39, proof p.40)

import Mathlib
import Definitions.Def_OMSRArbitrary_PerResource

open scoped BigOperators
open MeasureTheory
open StochasticRewardMatching.Decomposable (Instance Seeds unitSeeds)
noncomputable section

namespace OMSRArbitrary

/-- **Lemma 18** (arXiv:2611.03598, §5.1, p.24; restated p.39, proof p.40): pathwise, for every
`t` with `(i, t) ∈ E` and `δ_t(u) > 0`:
(A) `D_t ≤ g(u) − c(u) + c(u) w_t(u)`;
(B) if PG(u) probes at `t` a resource whose reduced price is at least `r_i p_{it}(1 − g(u))`, then
`e_t ≥ δ_t(u)` and `D_t ≤ (g(u) − c(u))σ_Λ(u) + c(u) w_t(u)`.
Overall, `D_t ≤ (g(u) − c(u)) v_t(u) + c(u) w_t(u)`.

Here `u = u_i`; `Λ ∈ [1, ∞]` is the bound on weight ratios (`ρ = 1/Λ`) and `0 ≤ c ≤ g`, the
standing assumptions of Section 5 (p.23). -/
theorem lemma_18 {n m : ℕ} (D : Instance n m) (hr : ∀ k, 0 < D.reward k)
    (hp : ∀ e ∈ D.edges, 0 < D.probability e)
    (g : ℝ → ℝ) (hg_cont : ContinuousOn g (Set.Icc 0 1)) (hg_mono : MonotoneOn g (Set.Icc 0 1))
    (hg_maps : Set.MapsTo g (Set.Icc 0 1) (Set.Icc 0 1)) (hg_one : g 1 < 1)
    (c : ℝ → ℝ) (hc_int : IntegrableOn c (Set.Icc 0 1))
    (hc_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ c x) (hc_le : ∀ x ∈ Set.Icc (0 : ℝ) 1, c x ≤ g x)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρr : ∀ j k, ρ * D.reward j ≤ D.reward k)
    (u : Seeds n) (hu : unitSeeds u) (i : Fin n) (z : Seeds m) (t : Fin m)
    (hit : (i, t) ∈ D.edges) (hδ : 0 < deltaW D g u i z t) :
    demand D g c ρ u i z t ≤ g (u i) - c (u i) + c (u i) * wt D g ρ u i z t ∧
    ((∃ k, pgProbe D g u Finset.univ 0 (corrOutcome D z) t = some k ∧
        D.reward i * D.probability (i, t) * (1 - g (u i)) ≤ reducedPrice D g u k t) →
      deltaW D g u i z t ≤ boost D g u i z t ∧
        demand D g c ρ u i z t ≤
          (g (u i) - c (u i)) * sigmaW g ρ (u i) + c (u i) * wt D g ρ u i z t) ∧
    demand D g c ρ u i z t ≤
      (g (u i) - c (u i)) * vt D g ρ u i z t + c (u i) * wt D g ρ u i z t := by sorry

end OMSRArbitrary
