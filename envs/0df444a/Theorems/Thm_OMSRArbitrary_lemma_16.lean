-- Prove2me | Theorems.Thm_OMSRArbitrary_lemma_16
-- name    : OMSRArbitrary.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:37:02.133623+00:00
-- url     : https://prove2.me/theorems/cb462d0c-803c-4c40-a27f-947b7a8033b4
-- title:
--   Lemma 16 — release arrivals do not depend on $z_\tau$
-- statement:
--   Throughout, $g:[0,1]\to[0,1]$ is continuous and nondecreasing with $g(1)<1$, every resource has a weight $r_i>0$ and every edge a success probability $p_{it}\in(0,1]$. Fix a resource $i$, seeds $u$ in $[0,1]$ and an arrival $\tau$.
--
--   **Lemma 16 (Restated).** Condition (i) of Definition F.2, the resource $J_\tau$ and the probability $p_{J_\tau\tau}$ are determined by $z_{<\tau}$, and condition (ii) is determined by $z_{-\tau}$. In particular, whether $\tau$ is a release arrival does not depend on $z_\tau$.
--
--   "Determined by $z_{<\tau}$" means equal for any two threshold vectors that agree before $\tau$; "determined by $z_{-\tau}$" means equal for any two that agree at every arrival other than $\tau$. This is what makes the averaging of Lemma F.3 legitimate.
--
--   Differences from the source:
--   - encoding: a finite set U of resources and arrivals t ∈ [T] = {1, …, T} → resources Fin n and arrivals Fin m, 0-based, for every n, m; reason: relabelling; every finite instance, including empty ones, is covered
--   - encoding: edge probabilities p_it ∈ (0,1] and weights r_i > 0 → the published Instance (r ≥ 0, p ∈ [0,1] on edges) with hypotheses 0 < r_k and 0 < p_e for e ∈ E; reason: the same instances
--   - encoding: g : [0,1] → [0,1] continuous and nondecreasing with g(1) < 1 → g : ℝ → ℝ with ContinuousOn, MonotoneOn and MapsTo on [0,1] and g 1 < 1; reason: only the values of g on [0,1] enter, since seeds lie in [0,1]
--   - encoding: ties broken in a fixed order of the resources → ties broken toward the smaller resource index; reason: resources can be relabelled, so every fixed order is the index order of some labelling
--   - encoding: determined by z_{<τ} / determined by z_{−τ} → equal for any two threshold vectors that agree before τ / agree off τ; reason: the meaning of "determined by"
--   - generalization: pathwise, for sample paths (thresholds z ∈ [0,1]^m) → for every z ∈ ℝ^m; reason: the claim holds verbatim for every threshold vector; restricting z to [0,1]^m gives the source statement
-- source:
--   Udwani, Online Matching with Arbitrary Stochastic Rewards, arXiv:2611.03598, Lemma 16, p.19 (restated for Definition F.2, p.41)

import Mathlib
import Definitions.Def_OMSRArbitrary_Releases

open scoped BigOperators
open MeasureTheory
open StochasticRewardMatching.Decomposable (Instance Seeds unitSeeds)
noncomputable section

namespace OMSRArbitrary

/-- **Lemma 16 (Restated)** (arXiv:2611.03598, App. F.2, p.41; Lemma 16, p.19): condition (i) of
Definition F.2, the resource `J_τ` and the probability `p_{Jτ}` are determined by `z_{<τ}`, and
condition (ii) is determined by `z_{−τ}`. In particular, whether `τ` is a release arrival does
not depend on `z_τ`.

"Determined by `z_{<τ}`" is: equal for any two threshold vectors that agree at every arrival
before `τ`; "determined by `z_{−τ}`" is: equal for any two that agree at every arrival other
than `τ`. -/
theorem lemma_16 {n m : ℕ} (D : Instance n m) (hr : ∀ k, 0 < D.reward k)
    (hp : ∀ e ∈ D.edges, 0 < D.probability e)
    (g : ℝ → ℝ) (hg_cont : ContinuousOn g (Set.Icc 0 1)) (hg_mono : MonotoneOn g (Set.Icc 0 1))
    (hg_maps : Set.MapsTo g (Set.Icc 0 1) (Set.Icc 0 1)) (hg_one : g 1 < 1)
    (u : Seeds n) (hu : unitSeeds u) (i : Fin n) (τ : Fin m) :
    (∀ z z' : Seeds m, (∀ t : Fin m, t < τ → z t = z' t) →
      (relCond1 D g u i z τ ↔ relCond1 D g u i z' τ) ∧
        bestAlt D g u Finset.univ 0 (corrOutcome D z) i τ =
          bestAlt D g u Finset.univ 0 (corrOutcome D z') i τ ∧
        (bestAlt D g u Finset.univ 0 (corrOutcome D z) i τ).map (fun J => D.probability (J, τ)) =
          (bestAlt D g u Finset.univ 0 (corrOutcome D z') i τ).map
            (fun J => D.probability (J, τ))) ∧
    (∀ z z' : Seeds m, (∀ t : Fin m, t ≠ τ → z t = z' t) →
      (relCond2 D g u i z τ ↔ relCond2 D g u i z' τ)) ∧
    (∀ z z' : Seeds m, (∀ t : Fin m, t ≠ τ → z t = z' t) →
      (IsReleaseArrival D g u i z τ ↔ IsReleaseArrival D g u i z' τ)) := by sorry

end OMSRArbitrary
