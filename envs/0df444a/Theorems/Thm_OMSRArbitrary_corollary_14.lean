-- Prove2me | Theorems.Thm_OMSRArbitrary_corollary_14
-- name    : OMSRArbitrary.corollary_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:38:46.947728+00:00
-- url     : https://prove2.me/theorems/5a1cb11d-efb3-448f-8896-5c9f3d81aeac
-- title:
--   Corollary 14 — no match of $i$ and no release give $T_i=\emptyset$ and $M=0$
-- statement:
--   Throughout, $g:[0,1]\to[0,1]$ is continuous and nondecreasing with $g(1)<1$, every resource has a weight $r_i>0$ and every edge a success probability $p_{it}\in(0,1]$. Let the weights lie within a factor $\Lambda\in[1,\infty]$ of each other and $c$ be integrable with $0\le c\le g$. Fix a resource $i$, seeds $u$ in $[0,1]$ and thresholds $z$.
--
--   **Corollary 14.** If PG$(u)$ never matches $i$ and never releases, then $T_i=\emptyset$ and $M=0$.
--
--   So a positive demand without a match of $i$ requires a release.
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
--   Udwani, Online Matching with Arbitrary Stochastic Rewards, arXiv:2611.03598, Corollary 14, p.18 (restated p.40)

import Mathlib
import Definitions.Def_OMSRArbitrary_PerResource
import Definitions.Def_OMSRArbitrary_Releases

open scoped BigOperators
open MeasureTheory
open StochasticRewardMatching.Decomposable (Instance Seeds unitSeeds)
noncomputable section

namespace OMSRArbitrary

/-- **Corollary 14** (arXiv:2611.03598, §4.2, p.18; restated with weights, p.40): if PG(u) never
matches `i` and never releases, then `T_i = ∅` and `M = 0`.

PG(u) is the run with seeds `u` from all resources on thresholds `z`; `T_i` and `M` are the
weighted quantities of Section 5.1 (p.24). -/
theorem corollary_14 {n m : ℕ} (D : Instance n m) (hr : ∀ k, 0 < D.reward k)
    (hp : ∀ e ∈ D.edges, 0 < D.probability e)
    (g : ℝ → ℝ) (hg_cont : ContinuousOn g (Set.Icc 0 1)) (hg_mono : MonotoneOn g (Set.Icc 0 1))
    (hg_maps : Set.MapsTo g (Set.Icc 0 1) (Set.Icc 0 1)) (hg_one : g 1 < 1)
    (c : ℝ → ℝ) (hc_int : IntegrableOn c (Set.Icc 0 1))
    (hc_nonneg : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ c x) (hc_le : ∀ x ∈ Set.Icc (0 : ℝ) 1, c x ≤ g x)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρr : ∀ j k, ρ * D.reward j ≤ D.reward k)
    (u : Seeds n) (hu : unitSeeds u) (i : Fin n) (z : Seeds m)
    (hnm : ¬ pgMatches D g u Finset.univ 0 (corrOutcome D z) i)
    (hnr : ∀ τ : Fin m, ¬ releasesAt D g u Finset.univ 0 z i τ) :
    Tset D g u i z = ∅ ∧ Mmax D g c ρ u i z = 0 := by sorry

end OMSRArbitrary
