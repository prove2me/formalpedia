-- Prove2me | Theorems.Thm_FreeOrderEPTAS_estimate
-- name    : FreeOrderEPTAS.estimate
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:26:42.042966+00:00
-- url     : https://prove2.me/theorems/3a55d2bb-cc31-4728-8a98-614b4f594e3e
-- title:
--   p.17 — $V(\sigma)\ge\frac12\mathrm{OPT}$ and the estimate $E$ (corrected: grid relative to $V(\sigma_0)$)
-- statement:
--   For every permutation $\sigma$,
--   $$V(\sigma)\ge\tfrac12\,\mathbb E\big[\max_{j\in[n]}X_j\big]\ge\tfrac12\mathrm{OPT}.$$
--   Moreover, if $\epsilon\in(0,1]$, then some $E=V(\sigma_0)(1+\epsilon)^k$ with $0\le k\le\lceil\log2/\log(1+\epsilon)\rceil$ lies in $[(1-\epsilon)\mathrm{OPT},\mathrm{OPT}]$.
--
--   The first part is the classical prophet inequality, and the published item `MatroidProphetKW.RankOne.half_mean_threshold` gives it for a threshold rule.
--
--   Differences from the source:
--   - correction: "all powers of $1+\epsilon$ within the interval $[V(\sigma),2V(\sigma)]$" → $V(\sigma_0)(1+\epsilon)^k$; reason: one variable with value $1.1$, $\epsilon=1/2$: then $V=\mathrm{OPT}=1.1$, the required $E\in[(1-\epsilon)\mathrm{OPT},\mathrm{OPT}]\cap[V,2V]$ is $1.1$, not a power of $1.5$
--   - encoding: $\max_{j\in[n]}X_j$ → `⨆ i, x i`, which is $0$ at $n=0$; reason: the supremum of a finite family; the empty case has value $0$ on both sides
--   - generalization: $1/\epsilon$ an integer → any $\epsilon\in(0,1]$; reason: the proof uses no integrality; the integer case is covered
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §3.2, p.17

import Mathlib
import Definitions.Def_FreeOrderEPTAS_OPT

open MeasureTheory

namespace FreeOrderEPTAS

/-- p.17 (arXiv:2007.13121v3): the prophet inequality `V(σ) ≥ ½ E[max_j X_j] ≥ ½ OPT` for every
`σ`, and some `E = V(σ₀)(1 + ϵ)^k` with `0 ≤ k ≤ ⌈log 2 / log(1 + ϵ)⌉` lies in
`[(1 - ϵ) OPT, OPT]`. -/
theorem estimate {n : ℕ} (I : Instance n) :
    (∀ σ, (∫ x : Fin n → ℝ, ⨆ i, x i ∂(Measure.pi I.μ)) / 2 ≤ V I σ) ∧
    OPT I ≤ ∫ x : Fin n → ℝ, ⨆ i, x i ∂(Measure.pi I.μ) ∧
    (∀ σ, OPT I ≤ 2 * V I σ) ∧
    ∀ (σ₀ : Equiv.Perm (Fin n)) (ϵ : ℝ), 0 < ϵ → ϵ ≤ 1 →
      ∃ k : ℕ, k ≤ ⌈Real.log 2 / Real.log (1 + ϵ)⌉₊ ∧
        (1 - ϵ) * OPT I ≤ V I σ₀ * (1 + ϵ) ^ k ∧ V I σ₀ * (1 + ϵ) ^ k ≤ OPT I := by sorry

end FreeOrderEPTAS
