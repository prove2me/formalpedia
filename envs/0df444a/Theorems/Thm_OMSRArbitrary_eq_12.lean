-- Prove2me | Theorems.Thm_OMSRArbitrary_eq_12
-- name    : OMSRArbitrary.eq_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:38:29.999171+00:00
-- url     : https://prove2.me/theorems/b4d10041-7b19-4ff1-ac12-b65594bb3986
-- title:
--   Eq. (12) — $\mathbb E[\prod_{t\in T_i}(1-w_t(u))]\ge\Pr[\mathrm{PG}(u)\text{ does not match }i]=Q_1(U)$
-- statement:
--   Throughout, $g:[0,1]\to[0,1]$ is continuous and nondecreasing with $g(1)<1$, every resource has a weight $r_i>0$ and every edge a success probability $p_{it}\in(0,1]$. Let the weights lie within a factor $\Lambda\in[1,\infty]$ of each other. Fix a resource $i$ and seeds $u=(u_k)$ in $[0,1]$, write $u=u_i$, and let expectations and probabilities be over the thresholds $z$ of the correlated model.
--
--   **Eq. (12).** For every such instance, every resource $i$ and every seed vector,
--   $$\mathbb E\Big[\prod_{t\in T_i}\big(1-w_t(u)\big)\Big]\ \ge\ \Pr[\mathrm{PG}(u)\text{ does not match }i]=Q_1(U),$$
--   where the empty product is $1$.
--
--   With $W\le1-\prod_{t\in T_i}(1-w_t(u))$ (eq. (10)) this gives Lemma 20(B).
--
--   Differences from the source:
--   - encoding: a finite set U of resources and arrivals t ∈ [T] = {1, …, T} → resources Fin n and arrivals Fin m, 0-based, for every n, m; reason: relabelling; every finite instance, including empty ones, is covered
--   - encoding: edge probabilities p_it ∈ (0,1] and weights r_i > 0 → the published Instance (r ≥ 0, p ∈ [0,1] on edges) with hypotheses 0 < r_k and 0 < p_e for e ∈ E; reason: the same instances
--   - encoding: g : [0,1] → [0,1] continuous and nondecreasing with g(1) < 1 → g : ℝ → ℝ with ContinuousOn, MonotoneOn and MapsTo on [0,1] and g 1 < 1; reason: only the values of g on [0,1] enter, since seeds lie in [0,1]
--   - encoding: ties broken in a fixed order of the resources → ties broken toward the smaller resource index; reason: resources can be relabelled, so every fixed order is the index order of some labelling
--   - encoding: Λ ∈ [1, ∞] and weights within a factor Λ of each other; σ_Λ = σ/Λ → ρ = 1/Λ ∈ [0,1] with ρ r_j ≤ r_k for all j, k; σ_Λ = ρ σ; reason: ρ = 0 is Λ = ∞ and ρ = 1 is Λ = 1
--   - encoding: E and Pr over the thresholds z with all seeds fixed (Sections 4–5, App. F) → integrals over z ∼ seedLaw m (i.i.d. uniform on [0,1]) at a fixed seed vector u ∈ [0,1]^n; reason: the correlated model draws z i.i.d. uniform on [0,1]
--   - encoding: Q_1(U) → neverMatchProb … 0 univ; reason: 0-based arrivals
-- source:
--   Udwani, Online Matching with Arbitrary Stochastic Rewards, arXiv:2611.03598, §5.2, proof of Lemma 20(B), eq. (12), p.27

import Mathlib
import Definitions.Def_OMSRArbitrary_PerResource
import Definitions.Def_OMSRArbitrary_NeverMatch

open scoped BigOperators
open MeasureTheory
open StochasticRewardMatching.Decomposable (Instance Seeds seedLaw unitSeeds)
noncomputable section

namespace OMSRArbitrary

open Classical in
/-- **Eq. (12)** (arXiv:2611.03598, §5.2, proof of Lemma 20(B), p.27): on every instance whose
weights lie within a factor `Λ` of each other, for every resource `i` and fixed seeds `u`,
`E[∏_{t∈T_i}(1 − w_t(u))] ≥ Pr[PG(u) does not match i] = Q_1(U)`.

Expectations are over the thresholds `z`; the empty product is `1`.

**Formalization Note.** `ρ = 1/Λ`; the paper's `Q_1(U)` is `neverMatchProb … 0 univ`
(0-based arrivals). -/
theorem eq_12 {n m : ℕ} (D : Instance n m) (hr : ∀ k, 0 < D.reward k)
    (hp : ∀ e ∈ D.edges, 0 < D.probability e)
    (g : ℝ → ℝ) (hg_cont : ContinuousOn g (Set.Icc 0 1)) (hg_mono : MonotoneOn g (Set.Icc 0 1))
    (hg_maps : Set.MapsTo g (Set.Icc 0 1) (Set.Icc 0 1)) (hg_one : g 1 < 1)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρr : ∀ j k, ρ * D.reward j ≤ D.reward k)
    (u : Seeds n) (hu : unitSeeds u) (i : Fin n) :
    ∫ z, (if pgMatches D g u Finset.univ 0 (corrOutcome D z) i then (0 : ℝ) else 1) ∂seedLaw m ≤
      ∫ z, (∏ t ∈ Tset D g u i z, (1 - wt D g ρ u i z t)) ∂seedLaw m ∧
    ∫ z, (if pgMatches D g u Finset.univ 0 (corrOutcome D z) i then (0 : ℝ) else 1) ∂seedLaw m =
      neverMatchProb D g u i 0 Finset.univ := by sorry

end OMSRArbitrary
