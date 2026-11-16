-- Prove2me | Theorems.Thm_LRTempElim_Supplement_theorem_3
-- name    : LRTempElim.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:38:36.493794+00:00
-- url     : https://prove2.me/theorems/35262f06-c490-4ff6-9235-33fb45823749
-- title:
--   Theorem 3 — sampleable paths: $\mathbb E\|\hat f-\ell^\star\|_{L^1(Q)}\le\mathcal B+\mathcal V/\sqrt N$, the capped-ratio bound (14), and capped-ratio consistency
-- statement:
--   Let $P,Q$ be probability measures with $P\ll Q$, $r=dP/dQ$, $0<r<\infty$ $Q$-almost surely and $\ell^\star=\log r\in L^1(Q)$. Let $W\sim\mu$ be a random input and $X_t=T_t(W)$ measurable sampling rules with endpoint laws $X_0\sim Q$ and $X_1\sim P$ (the nodes of one replica may share randomness), and let $W_1,\dots,W_N$ be independent copies of $W$. With the statistics (12), the constants (13) and $\hat r_M=\min\{e^{\hat f},M\}$, $\mathcal T_r(M)=\mathbb E_Q[(r-M)_+]$:
--
--   1. for every regular configuration (features $\phi$ fixed independently of the replicas, nodes $0=t_0<\dots<t_K=1$, ridge $\lambda>0$, $\Sigma_Q$ finite, $\sigma_{B,i},\sigma_{D,i}<\infty$ for every interval), every $N\ge1$ and every $M>0$,
--   $$
--   \mathbb E\|\hat f-\ell^\star\|_{L^1(Q)}\le\mathcal B_{k,K,\lambda}+\frac{\mathcal V_{k,K,\lambda}}{\sqrt N},\qquad \mathbb E\|\hat r_M-r\|_{L^1(Q)}\le M\Big(\mathcal B_{k,K,\lambda}+\frac{\mathcal V_{k,K,\lambda}}{\sqrt N}\Big)+\mathcal T_r(M); \tag{14}
--   $$
--   2. for a sequence of regular configurations (features, grids and ridges) indexed by $N$, write $a_N=\mathcal B_{k_N,K_N,\lambda_N}+\mathcal V_{k_N,K_N,\lambda_N}/\sqrt N$. If $a_N\to0$, $M_N\to\infty$ and $M_Na_N\to0$, then $\mathbb E\|\hat r_{M_N}-r\|_{L^1(Q)}\to0$;
--   3. if $r\le M$ $Q$-almost surely for a fixed $M>0$, the same conclusion holds with this fixed cap whenever $a_N\to0$.
--
--   The theorem gives finite-sample log-ratio and capped-ratio guarantees for the analytic readout on any path that can be sampled, with no independence across time nodes and no boundedness of $r$ or $\phi$; the capped ratio is consistent once the population bias and the sampling term vanish.
--
--   **Formalization Note** The expected errors are iterated lower Lebesgue integrals over $\mu^{\otimes N}$ and $Q$, with values in $[0,\infty]$; the right sides are the real constants (13) plus the tail in $[0,\infty]$. Interval $i$ runs from $t_i$ to $t_{i+1}$.
--
--   Differences from the source:
--   - generalization: P, Q with densities p, q on X ⊆ ℝᵈ, r = p/q → probability measures on any measurable space, r = dP/dQ; reason: when P ≪ Q, p/q = dP/dQ Q-a.e.; densities on ℝᵈ are a special case
--   - reading: "for fixed (P, Q) and a sequence of features, grids and ridges" → a sequence of regular configurations indexed by the replica count N, with the sampling rule T, the input law μ and (P, Q) fixed, and caps M_N > 0; reason: a_N is indexed by N; the cap is defined for M > 0
--   - encoding: "Σ_Q is finite", "σ_{B,i}, σ_{D,i} < ∞" → every coordinate of ϕ in L²(Q); every entry of B_i(W) and coordinate of D_i(W) in L²(μ); reason: a finite second moment is membership in L², which also makes the means B̄_i, d_i exist
--   - encoding: measurable sampling rules, ϕ fixed → T_t measurable for t ∈ [0,1], ϕ a measurable deterministic map; reason: the standing measurability of sampling rules and features
--   - encoding: c_Q = ∥Σ_Q^{1/2}∥_op → ∥Σ_Q∥_op^{1/2}; reason: equal for the positive semidefinite Σ_Q
--   - encoding: E∥·∥_{L¹(Q)} and T_r(M) → lower Lebesgue integrals in [0, ∞] over μ^{⊗N} and Q, compared with ENNReal.ofReal of the real right sides; reason: no junk value 0 for a non-integrable error
--   - encoding: N independent replicas (N implicit ≥ 1) → N ≥ 1 in (14); reason: excludes only the empty sample
-- source:
--   Chen, Wu, Yang, Zeng, Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination, STOC 2027 submission (manuscript of 2026-11-03, sha256 eee651394d60e9274fc77c5a1bd08841eb53ee6030924de85b47f5a195371758), Theorem 3, eqs. (12)–(14), p.8 (pdf p.10); §A.3, p.21 (pdf p.23)

import Mathlib
import Definitions.Def_LRTempElim_Supplement_SampleablePath

open MeasureTheory Matrix Set Filter Topology
open scoped ENNReal

namespace LRTempElim

namespace Supplement

/-- **Theorem 3** (Statistical guarantees for sampleable paths). Chen, Wu, Yang, Zeng,
*Likelihood-Ratio Learning under Weak Overlap via Analytic Temporal Elimination*, STOC 2027
submission (manuscript of 2026-11-03, sha256 eee65139…), Theorem 3 with eqs. (12)–(14), p.8
(pdf p.10); the sampling setting of §4.2 and §A.3, p.21 (pdf p.23).

"Suppose 0 < r = p/q < ∞ Q-almost surely, P ≪ Q, ℓ⋆ ∈ L¹(Q), Σ_Q is finite, and σ_{B,i},
σ_{D,i} < ∞ for every interval. For any M > 0, let r̂_M = min{e^{f̂}, M} and
T_r(M) = E_Q[(r − M)₊]. Then E∥f̂ − ℓ⋆∥_{L¹(Q)} ≤ B_{k,K,λ} + V_{k,K,λ}/√N,
E∥r̂_M − r∥_{L¹(Q)} ≤ M(B_{k,K,λ} + V_{k,K,λ}/√N) + T_r(M). (14) For fixed (P, Q) and a sequence
of features, grids and ridges, write a_N = B_{k_N,K_N,λ_N} + V_{k_N,K_N,λ_N}/√N. If a_N → 0,
M_N → ∞ and M_N a_N → 0, then E∥r̂_{M_N} − r∥_{L¹(Q)} → 0. If r ≤ M almost surely for a fixed M,
the same conclusion holds with this fixed cap whenever a_N → 0."

**Formalization Note.**
* `P`, `Q` are probability measures on a measurable space `X`, `r = dP/dQ` (`P.rnDeriv Q`), which
  is the paper's `p/q` `Q`-a.e.; `ℓ⋆ = log r`.
* The random input is `W ∼ μ` on a measurable space `Ω`, the sampling rule is `X_t = T t W` with
  `T t` measurable for `t ∈ [0, 1]`, and the endpoint laws are `X₀ ∼ Q`, `X₁ ∼ P`
  (`μ.map (T 0) = Q`, `μ.map (T 1) = P`). Nothing else is assumed about the path: nodes of one
  replica may share randomness. The `N` replicas are i.i.d. (`Measure.pi`).
* The configuration hypotheses (grid, `λ > 0`, measurable `ϕ`, `Σ_Q` finite, `σ_{B,i}, σ_{D,i} < ∞`)
  are `Config.Regular`. The bounds (14) hold for every regular configuration and every `N ≥ 1`.
* The expected errors are iterated lower Lebesgue integrals in `ℝ≥0∞` (no junk value for a
  non-integrable error); the right sides are `ENNReal.ofReal` of the real constants (13), plus the
  tail `T_r(M)` in `ℝ≥0∞`.
* Consistency: for every sequence of regular configurations `cs N` (features `ϕ_N` of dimension
  `k_N`, grids with `K_N` intervals, ridges `λ_N`; the path and `(P, Q)` fixed) and every cap
  sequence `M_N > 0`; and for a fixed cap `M > 0` with `r ≤ M` `Q`-a.s. -/
theorem theorem_3 {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (P Q : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : ℝ → Ω → X)
    (hPQ : P ≪ Q)
    (hr : ∀ᵐ x ∂Q, 0 < P.rnDeriv Q x ∧ P.rnDeriv Q x < ⊤)
    (hℓ : Integrable (logRatioRN P Q) Q)
    (hT : ∀ t ∈ Icc (0 : ℝ) 1, Measurable (T t))
    (hT0 : μ.map (T 0) = Q) (hT1 : μ.map (T 1) = P) :
    -- (14), for every configuration and every sample size N ≥ 1
    (∀ c : Config X, c.Regular Q μ T → ∀ N : ℕ, 1 ≤ N →
      c.expLogErr P Q μ T N ≤
          ENNReal.ofReal (c.constB P Q μ T + c.constV Q μ T / Real.sqrt N) ∧
        ∀ M : ℝ, 0 < M → c.expRatioErr P Q μ T N M ≤
          ENNReal.ofReal (M * (c.constB P Q μ T + c.constV Q μ T / Real.sqrt N)) +
            ratioTail P Q M) ∧
    -- capped-ratio consistency along a sequence of features, grids and ridges
    (∀ cs : ℕ → Config X, (∀ N, (cs N).Regular Q μ T) →
      (∀ Ms : ℕ → ℝ, (∀ N, 0 < Ms N) →
        Tendsto (fun N : ℕ => (cs N).constB P Q μ T + (cs N).constV Q μ T / Real.sqrt N)
          atTop (𝓝 0) →
        Tendsto Ms atTop atTop →
        Tendsto (fun N : ℕ =>
          Ms N * ((cs N).constB P Q μ T + (cs N).constV Q μ T / Real.sqrt N)) atTop (𝓝 0) →
        Tendsto (fun N : ℕ => (cs N).expRatioErr P Q μ T N (Ms N)) atTop (𝓝 0)) ∧
      (∀ M : ℝ, 0 < M → (∀ᵐ x ∂Q, P.rnDeriv Q x ≤ ENNReal.ofReal M) →
        Tendsto (fun N : ℕ => (cs N).constB P Q μ T + (cs N).constV Q μ T / Real.sqrt N)
          atTop (𝓝 0) →
        Tendsto (fun N : ℕ => (cs N).expRatioErr P Q μ T N M) atTop (𝓝 0))) := by sorry

end Supplement

end LRTempElim
