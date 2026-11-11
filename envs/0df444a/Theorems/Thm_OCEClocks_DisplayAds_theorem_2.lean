-- Prove2me | Theorems.Thm_OCEClocks_DisplayAds_theorem_2
-- name    : OCEClocks.DisplayAds.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:25:05.60068+00:00
-- url     : https://prove2.me/theorems/d79701b7-6a26-473c-9868-fb2e0f75e5c0
-- title:
--   Theorem 2 — Online Primal-Dual Allocation with First-Age Poisson OCEC ($\lambda=4.5$) is 0.556-competitive for Display Ads
-- statement:
--   **Display Ads.** There are finitely many advertisers $i$, known upfront, and finitely many impressions $j$ arriving in order. Impression $j$ reveals nonnegative weights $(w_{ij})_i$ and is allocated to at most one advertiser. The value of advertiser $i$ is $\max_{j\in S_i}w_{ij}$ (free disposal; $0$ if $S_i=\emptyset$). $\mathrm{OPT}$ is the weight of a maximum-weight matching between advertisers and impressions.
--
--   **The algorithm (§5.4), with $\lambda=4.5=9/2$.** Every advertiser runs an independent First-Age Poisson generator and keeps an age measure $\nu_{i,\ell}$ for each level $\ell>0$, initially $\pi=\mathrm{Exp}(\lambda)$. Its offer to impression $j$ at mass $y$ is
--
--   $$\Gamma^\star w_{ij}-\alpha_i(y)=\int_0^{w_{ij}}\nu_{i,\ell}M_y\Gamma\,d\ell-\int_{w_{ij}}^\infty\big(\Gamma^\star-\nu_{i,\ell}G_y\Gamma\big)\,d\ell\qquad(13)$$
--
--   ($\Gamma$, $\Gamma^\star$ from (6), (7)). Impression $j$ is processed in three steps:
--
--   1. allocate by water filling on these offers;
--   2. update the measures by (10);
--   3. round by OCEC rounding with the generators and a discard clock.
--
--   **Claim.** For every instance, every water-filling run $x$ of the algorithm satisfies
--
--   $$\mathbb E\Big[\sum_i\max_{j\in S_i}w_{ij}\Big]\ \ge\ 0.556\cdot\mathrm{OPT},$$
--
--   and such a run exists. The expectation is over the generators' Poisson processes and uniforms and over the discard clocks.
--
--   This improves the ratio $0.5368$ of the best earlier algorithm for edge-weighted online bipartite matching with free disposal.
--
--   **Formalization Note** Advertisers are `Fin m`, impressions `Fin n`, and the weights are any `w` with `0 ≤ w i j`. Water filling is described in the paper as a continuous process; here its outcome is characterised relationally by `IsWaterFillingRun (9/2) w x`, and the theorem asserts both that a run exists and that every run attains the bound. "0.556-competitive" is read as this inequality for every instance against the maximum-weight matching.
--
--   Differences from the source:
--   - encoding: finite sets I (resources) and J (requests), J indexed in arrival order → Fin m and Fin n, with the order of Fin n as the arrival order; reason: every finite ordered set is in bijection with some Fin
--   - encoding: the resource with the minimum clock wins (ties have probability zero) → ties in the minimum go to the smallest index; reason: a null event; a deterministic rule is needed to define S_i on every outcome
--   - encoding: expectations conditional on A(0) = a → the age process started at age a (last arrival at time −a, later arrivals at partial sums of i.i.d. Exp(λ) gaps, one independent Unif[0,1] for the request's clock); reason: this is how the paper evaluates these conditional expectations (proofs of Lemmas 16 and 32); by memorylessness it is the conditional law given A(0) = a
--   - reading: M⋆_x = lim_{ε↓0}(M_ε)^{x/ε}, formally exp(x L_M), in the potential Γ (6) and Γ⋆ = πΓ (7) → (M⋆_x 1)(a) is the probability that the infinitesimal-request age process started at age a has not stopped by time x; reason: the operator limit is informal in the paper; the paper identifies M⋆_x 1 with exactly this survival probability (p. 11 and the proof of Lemma 30)
--   - generalization: the allocation produced by the continuous water-filling procedure → every allocation satisfying the water-filling outcome conditions (IsWaterFillingRun), together with the existence of one; reason: the paper's proof uses only these outcome conditions (p. 17), and the procedure's output satisfies them, so the Lean claim implies the paper's
--   - reading: is 0.556-competitive for Display Ads → for every instance, E[Σ_i max_{j∈S_i} w_ij] ≥ 0.556 · OPT with OPT the maximum-weight matching weight, and a water-filling run exists; reason: the paper's benchmark is the offline optimum, the weight of a maximum-weight matching (p. 14); the existence clause excludes a vacuous statement
-- source:
--   Huang, Patton, Yang, Zhao, Online Correlated Exponential Clocks, STOC 2027 submission (manuscript of November 3, 2026, sha256 820333a3…), p. 14, Theorem 2 (algorithm pp. 16–17, §5.4; proof p. 17)

import Mathlib
import Definitions.Def_OCEClocks_DisplayAds_Algorithm

namespace OCEClocks.DisplayAds

/-- Theorem 2 (p. 14): with `λ = 4.5`, Online Primal-Dual Allocation with First-Age Poisson OCEC
(§5.4) is 0.556-competitive for Display Ads. For every instance, a water-filling run exists, and
every water-filling run, rounded by OCEC with First-Age Poisson generators, has expected total
value at least `0.556` times the weight of a maximum-weight matching. -/
theorem theorem_2 (m n : ℕ) (w : Fin m → Fin n → ℝ) (hw : ∀ i j, 0 ≤ w i j) :
    (∃ x : Fin m → Fin n → ℝ, IsWaterFillingRun (9 / 2) w x) ∧
    ∀ x : Fin m → Fin n → ℝ, IsWaterFillingRun (9 / 2) w x →
      (0.556 : ℝ) * OPT w ≤ expectedValue (9 / 2) w x := by sorry

end OCEClocks.DisplayAds
