-- Prove2me | Theorems.Thm_KellyStochasticNetworks_EffectiveBandwidth_many_sources
-- name    : KellyStochasticNetworks.EffectiveBandwidth.many_sources
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:48:13.999028+00:00
-- url     : https://prove2.me/theorems/a287101e-43cc-44ac-848c-c9fce6a392d2
-- title:
--   Theorem 6.10 — large deviations for a queue with many sources
-- statement:
--   Let $J$ be a fixed finite set of source classes and $n_j\in\mathbb N$ their base multiplicities. On a probability space, let $X_{ji}[a,b]$ be real workloads, measurable for each interval, nonnegative and additive over ordered adjacent intervals, and zero on intervals of length zero. The source processes are mutually independent; their whole-process distributions may depend on $j$ but not on $i$. Their increments are stationary: $X_{ji}[a,b]$ has the same law as $X_{ji}[0,b-a]$ for $a\le b$. For each class and each nonnegative finite duration, assume the exponential moment is finite in a neighborhood of zero, as in the chapter's local-MGF convention. Fix $C>0$ and $B>0$.
--
--   For each integer scale $N\ge1$, set
--   $$S^N[a,b]=\sum_{j\in J}\sum_{i=1}^{n_jN}X_{ji}[a,b],\qquad Q^N(0)=\sup_{t\ge0}\{S^N[-t,0]-CNt\}.$$
--   Assume these extended-real workloads are measurable, as required by their description as random variables, and let $L_N=P\{Q^N(0)>BN\}$. With $M_j(s,t)=\log\mathbb E[e^{sX_{j1}[0,t]}]$, the claimed limit is
--   $$\lim_{N\to\infty}\frac1N\log L_N=\sup_{t\ge0}\inf_{s\ge0}\left\{\sum_{j\in J}n_jM_j(s,t)-s(B+Ct)\right\}.$$
--   This is the chapter's many-sources, infinite-horizon buffer-overflow target. Finding F4 gives a counterexample to the printed claim even with positive buffer and stable bounded-rate stationary sources: the strict overflow probability can be zero while the variational rate is finite. The faithful statement is retained as printed and is expected to be disproved. Finding F1 separately records the sketch's unsupported infinite-time upper bound; no repair hypothesis is assumed.
--
--   **Formalization Note** All suprema, infima, and logarithmic rates here use extended reals, so $Q^N(0)=+\infty$ and $\log0=-\infty$ are retained. The source's $st\alpha_j(s,t)$ is represented by the log MGF itself, including the zero-tilt and zero-time boundaries. The scale is reindexed as $N+1$ and sources from zero. Nonnegative additive increments use the usual half-open interval convention for endpoint arrivals. Capacity and buffer are strictly positive, the regime in which both grow under scaling. The displayed source formulas are expanded directly in the Lean theorem to make its standalone blind audit self-contained; they agree with the model definition. No stability, temporal mixing, uniform-tail, or interior-optimizer assumption has been added to this goal.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed pp. 143–145 (PDF pp. 151–153), Theorem 6.10, Eqs. (6.4)–(6.5); DOI https://doi.org/10.1017/CBO9781139565363

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators ENNReal

namespace KellyStochasticNetworks.EffectiveBandwidth

theorem many_sources {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : J → ℕ → ℝ → ℝ → Ω → ℝ) (n : J → ℕ)
    (C B : ℝ) (hC : 0 < C) (hB : 0 < B)
    (hmeas : ∀ j i a b, Measurable (X j i a b))
    (hindep : iIndepFun
      (fun k : J × ℕ => fun ω => fun ab : ℝ × ℝ => X k.1 k.2 ab.1 ab.2 ω) P)
    (hident : ∀ j i, IdentDistrib
      (fun ω => fun ab : ℝ × ℝ => X j i ab.1 ab.2 ω)
      (fun ω => fun ab : ℝ × ℝ => X j 0 ab.1 ab.2 ω) P P)
    (hstationary : ∀ j i a b, a ≤ b →
      IdentDistrib (X j i a b) (X j i 0 (b - a)) P P)
    (hzero : ∀ j i a ω, X j i a a ω = 0)
    (hadd : ∀ j i a b d ω, a ≤ b → b ≤ d →
      X j i a d ω = X j i a b ω + X j i b d ω)
    (hnonneg : ∀ j i a b ω, a ≤ b → 0 ≤ X j i a b ω)
    (hlocal : ∀ j t, 0 ≤ t → ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s| < δ →
      Integrable (fun ω => Real.exp (s * X j 0 0 t ω)) P) :
    let S : ℕ → ℝ → ℝ → Ω → ℝ := fun N a b ω =>
      ∑ j, ∑ i ∈ Finset.range (n j * N), X j i a b ω
    let Q : ℕ → Ω → EReal := fun N ω =>
      ⨆ t : {t : ℝ // 0 ≤ t}, ((S N (-t.val) 0 ω - (C * N) * t.val : ℝ) : EReal)
    (∀ N, Measurable (Q N)) →
    Tendsto
      (fun N : ℕ => ((((N + 1 : ℕ) : ℝ)⁻¹ : EReal) *
        ENNReal.log (P {ω | ((B * (N + 1) : ℝ) : EReal) < Q (N + 1) ω})))
      atTop (𝓝 (⨆ t : {t : ℝ // 0 ≤ t}, ⨅ s : {s : ℝ // 0 ≤ s},
        (∑ j, (n j : EReal) *
          ENNReal.log (∫⁻ ω, ENNReal.ofReal (Real.exp (s.val * X j 0 0 t.val ω)) ∂P)) -
          ((s.val * (B + C * t.val) : ℝ) : EReal))) := by sorry

end KellyStochasticNetworks.EffectiveBandwidth
