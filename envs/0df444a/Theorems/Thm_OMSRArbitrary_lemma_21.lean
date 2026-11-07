-- Prove2me | Theorems.Thm_OMSRArbitrary_lemma_21
-- name    : OMSRArbitrary.lemma_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:37:23.377312+00:00
-- url     : https://prove2.me/theorems/1fde1d05-49bc-4be4-8e2c-501e18004be4
-- title:
--   Lemma 21 — $Q_t(A\setminus\{j\})\ge(1-\kappa_j)\,Q_t(A)$
-- statement:
--   Throughout, $g:[0,1]\to[0,1]$ is continuous and nondecreasing with $g(1)<1$, every resource has a weight $r_i>0$ and every edge a success probability $p_{it}\in(0,1]$. Fix a resource $i$ and seeds $u$ in $[0,1]$.
--
--   **Lemma 21.** For every arrival $t$ (including the base case $T+1$), every set $A$ of resources and every $j\in A\setminus\{i\}$,
--   $$Q_t(A\setminus\{j\})\ \ge\ (1-\kappa_j)\,Q_t(A).$$
--
--   Removing one resource lowers the probability that $i$ is never matched by at most the factor $1-\kappa_j$; it is the key step of eq. (12).
--
--   Differences from the source:
--   - encoding: a finite set U of resources and arrivals t ∈ [T] = {1, …, T} → resources Fin n and arrivals Fin m, 0-based, for every n, m; reason: relabelling; every finite instance, including empty ones, is covered
--   - encoding: edge probabilities p_it ∈ (0,1] and weights r_i > 0 → the published Instance (r ≥ 0, p ∈ [0,1] on edges) with hypotheses 0 < r_k and 0 < p_e for e ∈ E; reason: the same instances
--   - encoding: g : [0,1] → [0,1] continuous and nondecreasing with g(1) < 1 → g : ℝ → ℝ with ContinuousOn, MonotoneOn and MapsTo on [0,1] and g 1 < 1; reason: only the values of g on [0,1] enter, since seeds lie in [0,1]
--   - encoding: ties broken in a fixed order of the resources → ties broken toward the smaller resource index; reason: resources can be relabelled, so every fixed order is the index order of some labelling
--   - encoding: every arrival t ∈ [T] and the base T + 1 → t ∈ {0, …, m} (0-based), t = m being T + 1; reason: 0-based arrivals
--   - encoding: standing assumption of §5 (p.23) that the weights lie within a factor Λ ∈ [1, ∞] and 0 ≤ c ≤ g → no hypothesis on weight ratios and no c; reason: Λ = ∞ is allowed, so every instance satisfies the assumption, and neither Λ nor c enters the statement
-- source:
--   Udwani, Online Matching with Arbitrary Stochastic Rewards, arXiv:2611.03598, Lemma 21, p.26

import Mathlib
import Definitions.Def_OMSRArbitrary_NeverMatch

open scoped BigOperators
open MeasureTheory
open StochasticRewardMatching.Decomposable (Instance Seeds unitSeeds)
noncomputable section

namespace OMSRArbitrary

/-- **Lemma 21** (arXiv:2611.03598, §5.2, p.26): for every arrival `t`, every set `A` of resources
and every `j ∈ A \ {i}`, `Q_t(A \ {j}) ≥ (1 − κ_j) Q_t(A)`.

Seeds `u` are fixed.

**Formalization Note.** Arrivals are 0-based, so `t` ranges over `0, …, m`, where `t = m` is the
paper's base case `T + 1`. -/
theorem lemma_21 {n m : ℕ} (D : Instance n m) (hr : ∀ k, 0 < D.reward k)
    (hp : ∀ e ∈ D.edges, 0 < D.probability e)
    (g : ℝ → ℝ) (hg_cont : ContinuousOn g (Set.Icc 0 1)) (hg_mono : MonotoneOn g (Set.Icc 0 1))
    (hg_maps : Set.MapsTo g (Set.Icc 0 1) (Set.Icc 0 1)) (hg_one : g 1 < 1)
    (u : Seeds n) (hu : unitSeeds u) (i : Fin n)
    (t : ℕ) (ht : t ≤ m) (A : Finset (Fin n)) (j : Fin n) (hjA : j ∈ A) (hji : j ≠ i) :
    (1 - kappa D g u i j) * neverMatchProb D g u i t A ≤
      neverMatchProb D g u i t (A.erase j) := by sorry

end OMSRArbitrary
