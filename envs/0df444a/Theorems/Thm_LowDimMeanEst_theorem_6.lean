-- Prove2me | Theorems.Thm_LowDimMeanEst_theorem_6
-- name    : LowDimMeanEst.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:59:51.923191+00:00
-- url     : https://prove2.me/theorems/b218a14b-a704-4357-b5ba-4b7d92baa959
-- title:
--   Theorem 6 (corrected: Algorithm 2 returns the α = 0 solution when its search fails) — Algorithm 1 has error $\le\sigma(1+\eta)\sqrt{2\log(1/\delta)/n}$ w.p. $1-\delta$, with $\eta\to0$
-- statement:
--   **Theorem 6** (main theorem; corrected). For all constants $C_F,\Xi_F,\delta_F>0$ there are constants $\xi,\Xi,C>0$ and $\delta_0\in(0,1)$ such that both of the following hold, where $L=\log\frac1\delta$, $LL=\log\log\frac1\delta$ and
--
--   $$\eta=C\Big(\sqrt[4]{\tfrac Ln}+\tfrac1{LL}+\tfrac{d^2(\log d+LL)}{L}\Big(1+\sqrt{\tfrac dL}\Big)\Big).$$
--
--   1. **Error bound.** Let $\kappa$ be any family of initial estimators with Fact 49's guarantee with constants $(C_F,\Xi_F,\delta_F)$. Let $d\ge1$, $\delta\in(0,\delta_0)$, and $n=m+N$ with $|m-\sqrt{nL}|\le1$, $d\le\xi\sqrt{nL}$ and $n\ge\Xi L$. Let $D$ be any distribution on $\mathbb R^d$ with finite second moment, mean $\mu$, and variance at most $\sigma^2$ in every direction ($\sigma\ge0$; $\mu$ and $\sigma$ unknown to the algorithm). If $x_1,\dots,x_n$ are i.i.d. from $D$, then with probability at least $1-\delta$ every output $\hat\mu$ of Algorithm 1 (initial estimate $\kappa$ at confidence $\delta/2$ on the first $m$ samples, Algorithm 2 with correction C1 on the rest) satisfies
--   $$\|\hat\mu-\mu\|_2\ \le\ \sigma(1+\eta)\sqrt{\frac{2\log(1/\delta)}{n}} .$$
--   2. **Rate.** $\eta\to0$ as $\big(\frac Ln,\frac{d^2LL}{L}\big)\to(0,0)$, uniformly in $d\ge1$: for every $\varepsilon>0$ there is $\rho>0$ such that $\eta<\varepsilon$ whenever $d,n\ge1$, $\delta\in(0,\delta_0)$, $L/n<\rho$ and $d^2LL/L<\rho$.
--
--   The constant $\sqrt2$ is the one achieved by the sample mean of Gaussian data, and the $o(1)$ term depends on nothing but $d$, $n$ and $\delta$: in fixed or slowly growing dimension the estimator is sub-Gaussian with the sharp constant, for every distribution with finite covariance.
--
--   **Formalization Note** Algorithm 1 is a relation (Definition `Algorithm1`) and the failure event is "some output errs by more than the bound", so the bound holds for every way of resolving the algorithm's choices; probabilities of such events are outer measures. The initial estimator is any family with Fact 49's error guarantee (Definition `Fact49`), not a specific algorithm.
--
--   Differences from the source:
--   - correction: "Algorithm 2 outputs weights" on every input → Algorithm 2 is the relation IsTrimOutput: the printed search's outputs, or the α = 0 solution when the search has none; reason: if fewer than (1/3)log(1/δ) samples are nonzero the printed search has no output: a zero sample gets weight 0 at every α (all samples 0 under a point mass, a case Theorem 6 allows); the α = 0 solution is the limit of the binary search
--   - generalization: the estimator of Fact 49 ([DKP20], polynomial time, shift-scale-and-rotation equivariant) with its constants → every measurable estimator family with Fact 49's error guarantee, for every constants (C_F, Ξ_F, δ_F), required only for δ < δ_F; equivariance and running time not assumed; reason: [DKP20]'s estimator is one such family; the proof applies the guarantee to D directly and normalizes the remaining samples, using only Lemma 4
--   - generalization: √(n log(1/δ)) initial samples → every natural m with |m − √(n log(1/δ))| ≤ 1; reason: covers the floor and the ceiling of the printed non-integer count
--   - encoding: the initial estimate is the output of an algorithm → κ d m (δ/2) is measurable (part of the Fact 49 predicate); reason: the output map of an algorithm; the proof conditions on κ (p.14)
--   - encoding: "with probability at least 1 − δ … Algorithm 1 will output a µ̂ such that" → the outer measure of {x | some output µ̂ has ‖µ̂ − µ‖ > σ(1 + η)√(2L/n)} is ≤ δ; reason: Algorithm 1 is a relation; covers every selection of its output
--   - encoding: universal constants ξ, Ξ, δ upper bound, O(·) of η → ∀ C_F, Ξ_F, δ_F > 0, ∃ ξ, Ξ, δ0, C before the estimator, d, n, δ, D, σ; reason: constants independent of D and d, as the theorem says
--   - encoding: D with mean µ and variance ≤ σ² in all directions → probability measure with MemLp id 2 and E⟨X − µ, z⟩² ≤ σ² for unit z, σ ≥ 0; reason: the variance exists only with a finite second moment
--   - encoding: η = o(1), tends to 0 as (L/n, d²LL/L) → (0, 0) → ∀ ε > 0 ∃ ρ > 0 ∀ d, n ≥ 1, δ ∈ (0, δ0): L/n < ρ ∧ d²LL/L < ρ → η < ε; reason: the limit, uniformly in d, written with ε and ρ
--   - encoding: samples x₁, …, xₙ → Fin (m + N), 0-based; first m for κ, last N for Algorithm 2; reason: Lean convention; the split of the proof (p.14)
-- source:
--   Lee, Mathashery, Valiant, Wang, Optimal Sub-Gaussian Mean Estimation in Low Dimensions, STOC 2027 submission (manuscript sha256 7316d30e…), Theorem 6, pp.12–13 (proof pp.13–15)

import Mathlib
import Definitions.Def_LowDimMeanEst_Algorithm1
import Definitions.Def_LowDimMeanEst_Fact49
import Definitions.Def_LowDimMeanEst_Parameters

open MeasureTheory

namespace LowDimMeanEst

/-- **Theorem 6**, pp.12–13 (proof pp.13–15), with correction C1.

Lee, Mathashery, Valiant, Wang, *Optimal Sub-Gaussian Mean Estimation in Low Dimensions*, STOC 2027
submission (manuscript sha256 7316d30e…).

"There are universal constants ξ ≪ 1 and Ξ ≫ 1 such that the following holds. Consider a
distribution D on ℝᵈ with mean µ and variance ≤ σ² in all directions (µ, σ² both unknown), from which
n i.i.d. samples x₁, …, xₙ are drawn. If δ is upper bounded by a small universal constant, and
d ≤ ξ√(n log(1/δ)) and n ≥ Ξ log(1/δ), then with probability at least 1 − δ, Algorithm 1 on input δ
and the n samples will output a µ̂ such that ∥µ̂ − µ∥₂ ≤ σ(1 + η)√(2 log(1/δ)/n). Here, η = o(1) and
tends to 0 as (log(1/δ)/n, d² log log(1/δ)/log(1/δ)) → (0, 0), which also implies δ → 0 since d ≥ 1.
Explicitly, η = O(⁴√(log(1/δ)/n) + 1/log log(1/δ) + (d²(log d + log log(1/δ))/log(1/δ))
(1 + √(d/log(1/δ)))). Crucially, this o(1) term decays to 0 at a rate independent of the underlying
distribution D, except for the ambient dimensionality d."

**Formalization Note.**
* Constants. For every constant triple `(CF, ΞF, δF)` of Fact 49, there are `ξ, Ξ, δ0, C > 0`
  (`C` the constant of `η`'s `O(·)`, `η = etaMain C d n δ`) chosen before the estimator, `d`, `n`,
  `δ`, `D` and `σ`; so the `o(1)` term depends on nothing but `d`, `n`, `δ`.
* Algorithm 1 is the relation `IsAlg1Output` with Algorithm 2 corrected by C1 (`IsTrimOutput`: the
  printed search has no output when fewer than `(1/3) log(1/δ)` recentred samples are nonzero, and
  the `α = 0` solution is returned then). The initial estimate is `κ d m (δ/2)` on the first `m`
  samples, for **every** family `κ` of measurable estimators with Fact 49's guarantee
  (`IsFact49Estimator`), and for every `m` within `1` of `√(n log(1/δ))`; `n = m + N`.
* The failure event is "some output `µ̂` of Algorithm 1 has error above the bound", so the bound
  holds for every way of resolving the algorithm's choices; the measure of a set is its outer
  measure.
* `D` is any probability distribution on `ℝ^d` with finite second moment; `σ ≥ 0` bounds its
  variance in every unit direction (`CovLe D (σ²)`), `σ = 0` included.
* The second conjunct is the limit clause: `η < ε` once `log(1/δ)/n < ρ` and
  `d² log log(1/δ)/log(1/δ) < ρ`, uniformly in `d ≥ 1`.
-/
theorem theorem_6 :
    ∀ CF ΞF δF : ℝ, 0 < CF → 0 < ΞF → 0 < δF →
      ∃ ξ Ξ δ0 C : ℝ, 0 < ξ ∧ 0 < Ξ ∧ 0 < δ0 ∧ δ0 < 1 ∧ 0 < C ∧
        (∀ κ : (d : ℕ) → (m : ℕ) → ℝ → (Fin m → E d) → E d, IsFact49Estimator CF ΞF δF κ →
          ∀ (d m N : ℕ) (δ : ℝ), 1 ≤ d → 0 < δ → δ < δ0 →
            |(m : ℝ) - Real.sqrt (((m + N : ℕ) : ℝ) * logInv δ)| ≤ 1 →
            (d : ℝ) ≤ ξ * Real.sqrt (((m + N : ℕ) : ℝ) * logInv δ) →
            Ξ * logInv δ ≤ ((m + N : ℕ) : ℝ) →
            ∀ (D : Measure (E d)) [IsProbabilityMeasure D], ∀ σ : ℝ, 0 ≤ σ → CovLe D (σ ^ 2) →
              (Measure.pi fun _ : Fin (m + N) => D)
                  {x | ∃ muHat : E d, IsAlg1Output (κ d m (δ / 2)) δ x muHat ∧
                    σ * (1 + etaMain C d (m + N) δ) *
                        Real.sqrt (2 * logInv δ / ((m + N : ℕ) : ℝ)) <
                      ‖muHat - popMean D‖} ≤
                ENNReal.ofReal δ) ∧
        (∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
          ∀ (d n : ℕ) (δ : ℝ), 1 ≤ d → 1 ≤ n → 0 < δ → δ < δ0 →
            logInv δ / n < ρ → (d : ℝ) ^ 2 * loglogInv δ / logInv δ < ρ →
            etaMain C d n δ < ε) := by sorry

end LowDimMeanEst
