-- Prove2me | Theorems.Thm_OMSRArbitrary_lemma_13
-- name    : OMSRArbitrary.lemma_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:37:07.648614+00:00
-- url     : https://prove2.me/theorems/4979048b-5cb6-4ee9-89f3-31b5254e6737
-- title:
--   Lemma 13 — runs from $S\cup\{i\}$ and $S$ coincide without a match or release
-- statement:
--   Throughout, $g:[0,1]\to[0,1]$ is continuous and nondecreasing with $g(1)<1$, every resource has a weight $r_i>0$ and every edge a success probability $p_{it}\in(0,1]$. Fix seeds $u$ in $[0,1]$ and thresholds $z$.
--
--   **Lemma 13.** Consider two runs of PG from some arrival $s$ onward, with the same seeds and thresholds, starting from available sets $S\cup\{i\}$ (run 1) and $S$ (run 2), where $i\notin S$. Suppose run 1 neither matches $i$ nor releases at any arrival $t\ge s$. Then at every arrival $t\ge s$ the two runs have the same available resources other than $i$. Moreover, at every arrival where run 1 does not probe $i$, both runs probe the same resource with the same outcome.
--
--   A run that holds $i$ can therefore differ from the run without $i$ only through a match of $i$ or a release.
--
--   Differences from the source:
--   - encoding: a finite set U of resources and arrivals t ∈ [T] = {1, …, T} → resources Fin n and arrivals Fin m, 0-based, for every n, m; reason: relabelling; every finite instance, including empty ones, is covered
--   - encoding: edge probabilities p_it ∈ (0,1] and weights r_i > 0 → the published Instance (r ≥ 0, p ∈ [0,1] on edges) with hypotheses 0 < r_k and 0 < p_e for e ∈ E; reason: the same instances
--   - encoding: g : [0,1] → [0,1] continuous and nondecreasing with g(1) < 1 → g : ℝ → ℝ with ContinuousOn, MonotoneOn and MapsTo on [0,1] and g 1 < 1; reason: only the values of g on [0,1] enter, since seeds lie in [0,1]
--   - encoding: ties broken in a fixed order of the resources → ties broken toward the smaller resource index; reason: resources can be relabelled, so every fixed order is the index order of some labelling
--   - generalization: pathwise, for sample paths (thresholds z ∈ [0,1]^m) → for every z ∈ ℝ^m; reason: the claim holds verbatim for every threshold vector; restricting z to [0,1]^m gives the source statement
--   - encoding: the two runs have the same available resources other than i; same resource with the same outcome → the available sets with i erased are equal just before each arrival t ≥ s; equal probes and equal observed outcomes; reason: direct transcription
-- source:
--   Udwani, Online Matching with Arbitrary Stochastic Rewards, arXiv:2611.03598, Lemma 13, p.18 (restated p.40)

import Mathlib
import Definitions.Def_OMSRArbitrary_Releases

open scoped BigOperators
open MeasureTheory
open StochasticRewardMatching.Decomposable (Instance Seeds unitSeeds)
noncomputable section

namespace OMSRArbitrary

/-- **Lemma 13** (arXiv:2611.03598, §4.2, p.18; restated with weights, p.40): consider two runs of
PG from some arrival `s` onward, with the same seeds and thresholds, starting from available
sets `S ∪ {i}` (run 1) and `S` (run 2), where `i ∉ S`. Suppose run 1 neither matches `i` nor
releases at any arrival `t ≥ s`. Then at every arrival `t ≥ s` the two runs have the same
available resources other than `i`. Moreover, at every arrival where run 1 does not probe `i`,
both runs probe the same resource with the same outcome.

**Formalization Note.** Arrivals are 0-based; "at arrival `t`" is the available set just before
`t` is processed. -/
theorem lemma_13 {n m : ℕ} (D : Instance n m) (hr : ∀ k, 0 < D.reward k)
    (hp : ∀ e ∈ D.edges, 0 < D.probability e)
    (g : ℝ → ℝ) (hg_cont : ContinuousOn g (Set.Icc 0 1)) (hg_mono : MonotoneOn g (Set.Icc 0 1))
    (hg_maps : Set.MapsTo g (Set.Icc 0 1) (Set.Icc 0 1)) (hg_one : g 1 < 1)
    (u : Seeds n) (hu : unitSeeds u) (i : Fin n) (z : Seeds m)
    (S : Finset (Fin n)) (hiS : i ∉ S) (s : ℕ)
    (hrun : ∀ t : Fin m, s ≤ t.val →
      ¬ pgMatchesAt D g u (insert i S) s (corrOutcome D z) i t ∧
        ¬ releasesAt D g u (insert i S) s z i t) :
    (∀ t : Fin m, s ≤ t.val →
      (pgAvail D g u (insert i S) s (corrOutcome D z) t.val).erase i =
        (pgAvail D g u S s (corrOutcome D z) t.val).erase i) ∧
    (∀ t : Fin m, s ≤ t.val → pgProbe D g u (insert i S) s (corrOutcome D z) t ≠ some i →
      pgProbe D g u (insert i S) s (corrOutcome D z) t = pgProbe D g u S s (corrOutcome D z) t ∧
        pgOutcome D g u (insert i S) s (corrOutcome D z) t =
          pgOutcome D g u S s (corrOutcome D z) t) := by sorry

end OMSRArbitrary
