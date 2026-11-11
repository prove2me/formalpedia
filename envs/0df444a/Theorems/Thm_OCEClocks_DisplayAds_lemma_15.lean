-- Prove2me | Theorems.Thm_OCEClocks_DisplayAds_lemma_15
-- name    : OCEClocks.DisplayAds.lemma_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:25:02.719161+00:00
-- url     : https://prove2.me/theorems/5cd639c8-9fd2-4818-9310-a2f85f9bdb3d
-- title:
--   Lemma 15 — an uncovered level has probability at most the mass of its final age measure
-- statement:
--   Let $\lambda>0$, and consider a Display Ads instance with nonnegative weights $w_{ij}$. Fix fractional allocations $x_{ij}\in[0,1]$ with $\sum_ix_{ij}\le1$ for every impression $j$. Round them by OCEC rounding with independent First-Age Poisson generators of rate $\lambda$ and discard clocks, and let $S_i$ be the impressions allocated to advertiser $i$. For a level $w>0$ let $J_i(w)=\{j: w_{ij}\ge w\}$. Let $\nu_{i,w}$ be the final age measure, obtained from $\pi=\mathrm{Exp}(\lambda)$ by applying, impression by impression in arrival order, $M_{x_{ij}}$ if $w\le w_{ij}$ and $G_{x_{ij}}$ if $w>w_{ij}$ (update (10)). Then for every advertiser $i$ and level $w>0$,
--
--   $$\Pr\big[S_i\cap J_i(w)=\emptyset\big]\ \le\ \nu_{i,w}\mathbf 1.\qquad(11)$$
--
--   Integrated over levels, this bounds the expected value of advertiser $i$ from below by $\int_0^\infty(1-\nu_{i,w}\mathbf 1)\,dw$, the primal side of the analysis of Theorem 2.
--
--   **Formalization Note** The event is $\{\omega : w_{ij}<w \text{ for all } j\in S_i(\omega)\}$ under `roundingLaw (generatorLaw λ n) x`. The right side is the total mass `levelMeasure λ (w i) (x i) w n Set.univ`, compared in `ℝ≥0∞`.
--
--   Differences from the source:
--   - generalization: λ = 4.5 ("The rest of the paper fixes λ = 4.5", p. 9) → every λ > 0; reason: the printed statement does not depend on the value of λ; at λ = 9/2 the Lean statement is the paper's
--   - encoding: finite sets I (resources) and J (requests), J indexed in arrival order → Fin m and Fin n, with the order of Fin n as the arrival order; reason: every finite ordered set is in bijection with some Fin
--   - encoding: the resource with the minimum clock wins (ties have probability zero) → ties in the minimum go to the smallest index; reason: a null event; a deterministic rule is needed to define S_i on every outcome
--   - encoding: expectations conditional on A(0) = a → the age process started at age a (last arrival at time −a, later arrivals at partial sums of i.i.d. Exp(λ) gaps, one independent Unif[0,1] for the request's clock); reason: this is how the paper evaluates these conditional expectations (proofs of Lemmas 16 and 32); by memorylessness it is the conditional law given A(0) = a
-- source:
--   Huang, Patton, Yang, Zhao, Online Correlated Exponential Clocks, STOC 2027 submission (manuscript of November 3, 2026, sha256 820333a3…), p. 15, Lemma 15, eq. (11)

import Mathlib
import Definitions.Def_OCEClocks_DisplayAds_Algorithm

open MeasureTheory

namespace OCEClocks.DisplayAds

/-- Lemma 15 (p. 15), inequality (11): for every advertiser `i` and level `w > 0`, the probability
that `i` receives no impression of weight at least `w` is at most the total mass of the final
level measure `ν_{i,w}`. -/
theorem lemma_15 (lam : ℝ) (hlam : 0 < lam) (m n : ℕ) (w : Fin m → Fin n → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (x : Fin m → Fin n → ℝ) (hx : ∀ i j, x i j ∈ Set.Icc (0 : ℝ) 1)
    (hsum : ∀ j, ∑ i, x i j ≤ 1) (i : Fin m) (ℓ : ℝ) (hℓ : 0 < ℓ) :
    roundingLaw (generatorLaw lam n) x
        {ω | ∀ j ∈ allocated (firstAgeGenerator lam n) x ω i, w i j < ℓ} ≤
      levelMeasure lam (w i) (x i) ℓ n Set.univ := by sorry

end OCEClocks.DisplayAds
