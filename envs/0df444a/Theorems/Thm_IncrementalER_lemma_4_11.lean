-- Prove2me | Theorems.Thm_IncrementalER_lemma_4_11
-- name    : IncrementalER.lemma_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:05:05.1455+00:00
-- url     : https://prove2.me/theorems/ab856a95-1b57-436a-89e5-87eeb3278f70
-- title:
--   Lemma 4.11, pp.22–23 — stochastic multiplicative weights, bound (13) with probability $1-\gamma$
-- statement:
--   Let $V$ be a set of $n\ge1$ coordinates and $T\ge1$. On a probability space, let $\mathcal F_{t-1}\subseteq\mathcal G_t\subseteq\mathcal F_t$ be σ-algebras for $t\ge1$ ($\mathcal G_t$ contains the random choices before round $t$ and those that determine $g_t$). Start from $w_0\equiv1$ and let $p_t(v)=w_{t-1}(v)/\sum_uw_{t-1}(u)$. In round $t$:
--
--   1. the feedback $g_t\in\mathbb R^V$ is $\mathcal G_t$-measurable, $|g_t(v)|\le\rho$ for every $v$, and $\sum_vp_t(v)g_t(v)\le\alpha$;
--   2. for every $v$, the $\mathcal F_t$-measurable random variables $Y_{t,1}(v),\dots,Y_{t,N_t}(v)$, with $N_t$ $\mathcal G_t$-measurable, are conditionally independent given $\mathcal G_t$ and satisfy
--   $$|Y_{t,i}(v)|\le\rho,\tag{9}$$
--   $$\Big|\mathbb E\Big[\sum_{i=1}^{N_t}Y_{t,i}(v)\,\Big|\,\mathcal G_t\Big]-g_t(v)\Big|\le\delta,\tag{10}$$
--   $$\sum_{i=1}^{N_t}\mathbb E[Y_{t,i}(v)^2\mid\mathcal G_t]\le\nu;\tag{11}$$
--   3. $w_t(v)=w_{t-1}(v)\exp\big(\eta\sum_{i=1}^{N_t}Y_{t,i}(v)\big)$ (12), with $0<\eta\le1/(2(\rho+\delta))$.
--
--   No independence between different coordinates is required. Then for every $\gamma>0$, with probability at least $1-\gamma$, simultaneously for every $v\in V$,
--
--   $$\frac1T\sum_{t=1}^Tg_t(v)\le\alpha+2\delta+\eta\big(2\nu+(\rho+\delta)^2\big)+\frac{2\log(2n/\gamma)}{\eta T}.\tag{13}$$
--
--   This lets the batch update run the MWU with sparse sampled feedback whose error does not depend on $N_t$.
--
--   Differences from the source:
--   - encoding: random variables Y_{t,1}(v), …, Y_{t,N_t}(v), conditionally independent given G_t, satisfying (9) → a sequence Y_{t,i}(v), i ∈ ℕ, conditionally independent given G_t and bounded by ρ, of which the first N_t enter the update; reason: the paper's batch extended by zeros satisfies these, since N_t is G_t-measurable; the sums are unchanged
--   - encoding: (10): |E[∑_{i≤N_t} Y_{t,i}(v) | G_t] − g_t(v)| ≤ δ → |∑_{i≤N_t} E[Y_{t,i}(v) | G_t] − g_t(v)| ≤ δ almost surely; reason: equal since N_t is G_t-measurable; this is m_t(v) of p.59 and needs no integrability of the random-length sum
--   - encoding: G_t "contains all the random choices made before iteration t" and those determining g_t; F_t the history after round t → σ-algebras with F_{t−1} ≤ G_t ≤ F_t ≤ the ambient σ-algebra, g_t and N_t G_t-measurable, Y_{t,i} F_t-measurable; reason: the filtration of the proof, p.59
--   - reading: η ≤ 1/(2(ρ + δ)) → 0 < η and 2(ρ + δ)η ≤ 1; reason: the proof assumes 0 < η (p.59); the product form is the same condition and also covers ρ + δ = 0
--   - encoding: with probability at least 1 − γ, (13) holds for every v → the outer measure of the set where (13) fails for some v is at most γ; reason: an upper bound on the failure set needs no measurability and is the stronger form
--   - encoding: conditional independence → conditional probabilities of finite intersections factor almost surely (CondIndepSeq); reason: the standard definition; Mathlib's iCondIndepFun would add a standard Borel assumption
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Lemma 4.11 and (9)–(13), pp.22–23; setting of its proof, Appendix A.1, p.59

import Mathlib
import Definitions.Def_IncrementalER_mwuWeight

namespace IncrementalER

open MeasureTheory

/-- **Lemma 4.11** (stochastic multiplicative weights).

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), Lemma 4.11 with (9)–(13),
pp.22–23; the setting of its proof, Appendix A.1, p.59 (`F_{t−1} ⊆ G_t ⊆ F_t`, `N_t` determined
before sampling and included in `G_t`).

Let `V` be a set of `n ≥ 1` coordinates and `T ≥ 1`. On a probability space with σ-algebras
`F_{t−1} ⊆ G_t ⊆ F_t`, let the feedback `g_t` be `G_t`-measurable with `|g_t(v)| ≤ ρ` and
`∑_v p_t(v) g_t(v) ≤ α`, where `p_t` are the weights of the update (12),
`w_t(v) = w_{t−1}(v) exp(η ∑_{i=1}^{N_t} Y_{t,i}(v))`, `w_0 ≡ 1`. Suppose that for every `v` the
`F_t`-measurable `Y_{t,i}(v)` are conditionally independent given `G_t`, with `N_t`
`G_t`-measurable, and satisfy (9) `|Y_{t,i}(v)| ≤ ρ`, (10)
`|E[∑_{i=1}^{N_t} Y_{t,i}(v) | G_t] − g_t(v)| ≤ δ`, (11) `∑_{i=1}^{N_t} E[Y_{t,i}(v)² | G_t] ≤ ν`. If
`η ≤ 1/(2(ρ + δ))`, then for every `γ > 0`, with probability at least `1 − γ`, simultaneously for
every `v`, (13) `(1/T) ∑_{t=1}^T g_t(v) ≤ α + 2δ + η(2ν + (ρ + δ)²) + 2 log(2n/γ)/(ηT)`.

**Formalization Note.**
* Rounds are `t = 1, …, T`; the hypotheses are imposed for those rounds. The batch of round `t` is
  the sequence `Y t i v`, `i ∈ ℕ`, of which the first `N t ω` enter the update; (9) and the
  conditional independence are required of the whole sequence. The paper's batch
  `Y_{t,1}, …, Y_{t,N_t}` is extended by zeros, which keeps (9), the independence (`N_t` is
  `G_t`-measurable) and both sums.
* Since `N_t` is `G_t`-measurable, `E[∑_{i ≤ N_t} Y_{t,i}(v) | G_t] = ∑_{i ≤ N_t} E[Y_{t,i}(v) | G_t]`;
  (10) is stated in the second form (the `m_t(v)` of p.59), which needs no integrability of the
  random-length sum. Conditional expectations are Mathlib's `condExp`, and (10), (11) hold almost
  surely.
* `η ≤ 1/(2(ρ + δ))` is written `2(ρ + δ)η ≤ 1`, with `η > 0` (p.59). "With probability at least
  `1 − γ`" is an upper bound `γ` on the outer measure of the failure set. `log` is natural. -/
theorem lemma_4_11 {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {V : Type*} [Fintype V] [Nonempty V] (T : ℕ) (hT : 1 ≤ T) (ρ α δ ν η γ : ℝ)
    (hη : 0 < η) (hηR : 2 * (ρ + δ) * η ≤ 1) (hγ : 0 < γ)
    (F G : ℕ → MeasurableSpace Ω) (hF : ∀ t, F t ≤ mΩ)
    (hFG : ∀ t, 1 ≤ t → F (t - 1) ≤ G t ∧ G t ≤ F t)
    (g : ℕ → V → Ω → ℝ) (N : ℕ → Ω → ℕ) (Y : ℕ → ℕ → V → Ω → ℝ)
    (hg_meas : ∀ t ∈ Finset.Icc 1 T, ∀ v, Measurable[G t] (g t v))
    (hN_meas : ∀ t ∈ Finset.Icc 1 T, Measurable[G t] (N t))
    (hY_meas : ∀ t ∈ Finset.Icc 1 T, ∀ i v, Measurable[F t] (Y t i v))
    (hwidth : ∀ t ∈ Finset.Icc 1 T, ∀ v ω, |g t v ω| ≤ ρ)
    (horacle : ∀ t ∈ Finset.Icc 1 T, ∀ ω,
      ∑ v, mwuDist η (fun s u => ∑ i ∈ Finset.range (N s ω), Y s i u ω) t v * g t v ω ≤ α)
    (hindep : ∀ t ∈ Finset.Icc 1 T, ∀ v, CondIndepSeq (G t) μ (fun i => Y t i v))
    (h9 : ∀ t ∈ Finset.Icc 1 T, ∀ i v ω, |Y t i v ω| ≤ ρ)
    (h10 : ∀ t ∈ Finset.Icc 1 T, ∀ v, ∀ᵐ ω ∂μ,
      |∑ i ∈ Finset.range (N t ω), condExp (G t) μ (Y t i v) ω - g t v ω| ≤ δ)
    (h11 : ∀ t ∈ Finset.Icc 1 T, ∀ v, ∀ᵐ ω ∂μ,
      ∑ i ∈ Finset.range (N t ω), condExp (G t) μ (fun ω' => Y t i v ω' ^ 2) ω ≤ ν) :
    μ {ω | ∃ v : V, ¬ ((1 / (T : ℝ)) * ∑ t ∈ Finset.Icc 1 T, g t v ω ≤
        α + 2 * δ + η * (2 * ν + (ρ + δ) ^ 2) +
          2 * Real.log (2 * Fintype.card V / γ) / (η * T))} ≤ ENNReal.ofReal γ := by sorry

end IncrementalER
