-- Prove2me | Theorems.Thm_OMSRArbitrary_lemma_F_3
-- name    : OMSRArbitrary.lemma_F_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:37:28.597709+00:00
-- url     : https://prove2.me/theorems/5fd3b00a-076e-4c6e-8102-8ee3c10fdc48
-- title:
--   Lemma F.3 — $\mathbb E[\hat a_\tau\mid z_{-\tau}]=\mathbb E[a_\tau\mid z_{-\tau}]$ and $\mathbb E[\sum_\tau\hat a_\tau]=\Pr[\mathrm{PG}(u)\text{ matches }i]$
-- statement:
--   Throughout, $g:[0,1]\to[0,1]$ is continuous and nondecreasing with $g(1)<1$, every resource has a weight $r_i>0$ and every edge a success probability $p_{it}\in(0,1]$. Fix a resource $i$ and seeds $u=(u_k)$ in $[0,1]$, write $u=u_i$, and let expectations and probabilities be over the thresholds $z$ of the correlated model.
--
--   **Lemma F.3 (Weighted form of Lemma 17).** For every arrival $\tau$,
--   $$\mathbb E[\hat a_\tau\mid z_{-\tau}]=\mathbb E[a_\tau\mid z_{-\tau}].$$
--   Consequently, $\mathbb E\big[\sum_\tau\hat a_\tau\big]=\Pr[\mathrm{PG}(u)\text{ matches }i]$.
--
--   The conditional expectation given $z_{-\tau}$ is the average over the threshold $z_\tau\in[0,1]$ with the other thresholds fixed.
--
--   Differences from the source:
--   - encoding: a finite set U of resources and arrivals t ∈ [T] = {1, …, T} → resources Fin n and arrivals Fin m, 0-based, for every n, m; reason: relabelling; every finite instance, including empty ones, is covered
--   - encoding: edge probabilities p_it ∈ (0,1] and weights r_i > 0 → the published Instance (r ≥ 0, p ∈ [0,1] on edges) with hypotheses 0 < r_k and 0 < p_e for e ∈ E; reason: the same instances
--   - encoding: g : [0,1] → [0,1] continuous and nondecreasing with g(1) < 1 → g : ℝ → ℝ with ContinuousOn, MonotoneOn and MapsTo on [0,1] and g 1 < 1; reason: only the values of g on [0,1] enter, since seeds lie in [0,1]
--   - encoding: ties broken in a fixed order of the resources → ties broken toward the smaller resource index; reason: resources can be relabelled, so every fixed order is the index order of some labelling
--   - encoding: E and Pr over the thresholds z with all seeds fixed (Sections 4–5, App. F) → integrals over z ∼ seedLaw m (i.i.d. uniform on [0,1]) at a fixed seed vector u ∈ [0,1]^n; reason: the correlated model draws z i.i.d. uniform on [0,1]
--   - encoding: E[· | z_{−τ}] → the integral over the τ-th threshold x ∈ [0,1] of the function at Function.update z τ x; reason: z_τ is uniform on [0,1] and independent of z_{−τ}
--   - generalization: E[â_τ | z_{−τ}] = E[a_τ | z_{−τ}] (almost surely) → the equality for every z ∈ ℝ^m; reason: it holds for every value of z_{−τ}; almost sure equality follows
--   - generalization: standing assumption of App. F that all weights lie within a factor Λ → no hypothesis on weight ratios; reason: the statement does not involve Λ; adding the hypothesis gives the source statement
-- source:
--   Udwani, Online Matching with Arbitrary Stochastic Rewards, arXiv:2611.03598, Lemma F.3, p.41

import Mathlib
import Definitions.Def_OMSRArbitrary_Releases

open scoped BigOperators
open MeasureTheory
open StochasticRewardMatching.Decomposable (Instance Seeds seedLaw unitSeeds)
noncomputable section

namespace OMSRArbitrary

/-- **Lemma F.3** (Weighted Form of Lemma 17; arXiv:2611.03598, App. F.2, p.41): for every
arrival `τ`, `E[â_τ | z_{−τ}] = E[a_τ | z_{−τ}]`. Consequently,
`E[∑_τ â_τ] = Pr[PG(u) matches i]`.

Seeds `u` are fixed; expectations are over the thresholds `z`.

**Formalization Note.** `E[· | z_{−τ}]` is the integral over the `τ`-th threshold `x ∈ [0,1]`
with the other thresholds of `z` fixed (`Function.update z τ x`), stated for every `z`. -/
theorem lemma_F_3 {n m : ℕ} (D : Instance n m) (hr : ∀ k, 0 < D.reward k)
    (hp : ∀ e ∈ D.edges, 0 < D.probability e)
    (g : ℝ → ℝ) (hg_cont : ContinuousOn g (Set.Icc 0 1)) (hg_mono : MonotoneOn g (Set.Icc 0 1))
    (hg_maps : Set.MapsTo g (Set.Icc 0 1) (Set.Icc 0 1)) (hg_one : g 1 < 1)
    (u : Seeds n) (hu : unitSeeds u) (i : Fin n) :
    (∀ (τ : Fin m) (z : Seeds m),
      ∫ x in (0 : ℝ)..1, aHat D g u i (Function.update z τ x) τ =
        ∫ x in (0 : ℝ)..1, aInd D g u i (Function.update z τ x) τ) ∧
    ∫ z, (∑ τ : Fin m, aHat D g u i z τ) ∂seedLaw m = matchProb D g u i := by sorry

end OMSRArbitrary
