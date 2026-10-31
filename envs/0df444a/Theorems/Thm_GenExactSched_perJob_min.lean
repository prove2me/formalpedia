-- Prove2me | Theorems.Thm_GenExactSched_perJob_min
-- name    : GenExactSched.perJob_min
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:45:49.382782+00:00
-- url     : https://prove2.me/theorems/a6c214a1-3583-4c25-b128-8681ed8b648a
-- title:
--   Proof of Lemma 9, (98)–(104) — per-job minimization of $s^2/T+\delta(\sigma-s)+\varepsilon(T-\tau)$ (corrected: indicators of (26), no uniqueness at $\varepsilon=\delta^2/4$)
-- statement:
--   Fix unit costs $\delta\ge0$, $\varepsilon>0$ and a job with $0\le\sigma\le\tau$. A job that receives service $s\in[0,\sigma]$ over an actual sojourn time $T\ge\tau$ costs at least
--
--   $$C(s,T)=\frac{s^2}{T}+\delta(\sigma-s)+\varepsilon(T-\tau)$$
--
--   (the flat-rate variance bound plus both penalties). Let $s^*=\hat\sigma_{v^*}(\sigma,\tau)$ and $T^*=\tau+\mathrm{ext}_{v^*}(\sigma,\tau)$ be the service and the sojourn time of the profile (96). Then:
--
--   1. $C(s,T)\ge J^*(\sigma,\tau)$ for every $s\in[0,\sigma]$ and $T\ge\tau$, where $J^*$ is the corrected integrand of (26);
--   2. $(s^*,T^*)$ is admissible ($0\le s^*\le\sigma$, $T^*\ge\tau$, finite extension) and $C(s^*,T^*)=J^*(\sigma,\tau)$;
--   3. if $\varepsilon\ne\delta^2/4$, $(s^*,T^*)$ is the only admissible pair with $C(s,T)=J^*(\sigma,\tau)$;
--   4. if $\delta^2/4\le\varepsilon$, then $T^*=\tau$ (no deadline is extended), and if $\delta^2/4>\varepsilon$, then $s^*=\sigma$ (every demand is met).
--
--   This is the pointwise step that reduces Lemma 9, and hence Theorem 4, to a two-variable minimization per job.
--
--   **Formalization Note** The printed chain (101)–(102) contains slips (the case hypothesis is contradicted and a constant is off); the conclusion stated here is the one the proof needs. The job with $\sigma=\tau=0$ is included: there every quantity is $0$.
--
--   Differences from the source:
--   - correction: (26) with indicators 1{σ/τ > δ/2 ≥ √ε} and 1{σ/τ > √ε > δ/2} → J* with indicators 1{σ/τ > δ/2, δ/2 ≤ √ε} and 1{σ/τ > √ε, √ε < δ/2}; reason: the printed indicators are reversed: at σ = 3/4, τ = 1, δ = 2, ε = 1/4 none fires, so printed (26) is 0 while every policy costs at least 1/2 per job (paper.md item 2).
--   - correction: "the optimal σ̂*(σ, τ) and τ̂*(σ, τ)" as the unique minimizer in every case → uniqueness of (s*, T*) only when ε ≠ δ²/4; at ε = δ²/4 only the value and the regime facts; reason: at σ = τ = 1, δ = 1, ε = 1/4 both (1/2, 1) and (1, 2) cost 3/4 (paper.md item 8).
--   - reading: "the point-wise maximum of the integrand of (97)" over σ̂ ≥ σ, τ̂ ≥ τ → the minimum of C(s, T) over 0 ≤ s ≤ σ, T ≥ τ; reason: (97) is an infimum, so "maximum" means minimum; σ̂ ≥ σ is a slip for (80) σ̂ ≤ σ (paper.md item 6).
--   - encoding: the functions σ̂(σ, τ), τ̂(σ, τ) of a profile → real numbers s, T for one job, with (s*, T*) read off the profile (96) as (σ̂_{v*}(σ, τ), τ + ext_{v*}(σ, τ)); reason: the minimization is pointwise in the job type.
--   - encoding: unit costs δ, ε without stated signs → 0 ≤ δ and 0 < ε as hypotheses; reason: unit costs; ε > 0 as in the goal (paper.md item 7).
--   - encoding: σ/τ and σ²/τ for a job with τ = 0 → Lean's x / 0 = 0; reason: on S, τ = 0 forces σ = 0, where the job costs 0 and is served at rate 0; no instance changes.
-- source:
--   Nakahira–Ferragut–Wierman, Generalized Exact Scheduling: A Minimal-Variance Distributed Deadline Scheduler, arXiv:2004.12280v2, proof of Lemma 9, the cost C(σ, τ̂) and (98)–(104), p. 42 (problem (97), p. 41)

import Mathlib
import Definitions.Def_GenExactSched_Model

open MeasureTheory
open scoped ENNReal NNReal

namespace GenExactSched

/-- **Per-job minimization in the proof of Lemma 9**, Nakahira–Ferragut–Wierman,
arXiv:2004.12280v2, proof of Lemma 9, the cost `C(σ, τ̂)` and (98)–(104), p. 42.

Fix `0 ≤ δ`, `0 < ε` and a job with `0 ≤ σ ≤ τ`. For a service amount `s ∈ [0, σ]` and an
actual sojourn time `T ≥ τ`, the per-job cost is `s²/T + δ(σ − s) + ε(T − τ)`. Let `s* = σ̂_{v*}(σ, τ)`
and `T* = τ + ext_{v*}(σ, τ)` be the service and sojourn time of the profile (96). Then

1. every `(s, T)` costs at least `J*(σ, τ)` (the corrected integrand of (26));
2. `(s*, T*)` is admissible (`0 ≤ s* ≤ σ`, `T* ≥ τ`, the extension is finite) and costs exactly
   `J*(σ, τ)`;
3. if `ε ≠ δ²/4`, `(s*, T*)` is the only admissible pair costing `J*(σ, τ)`;
4. if `δ²/4 ≤ ε`, then `T* = τ` (no deadline is extended), and if `δ²/4 > ε`, then `s* = σ`
   (every demand is met).

**Formalization Note.** The printed chain (101)–(102) contains slips (the case hypothesis is
contradicted and a constant is off); the conclusion stated here is the one the proof needs. At
`ε = δ²/4` the minimizer is not unique (`σ = τ = 1`, `δ = 1`: `(1/2, 1)` and `(1, 2)` both cost
`3/4`). The job `σ = τ = 0` is included; there every quantity is `0`. -/
theorem perJob_min (δ ε σ τ : ℝ) (hδ : 0 ≤ δ) (hε : 0 < ε) (hσ : 0 ≤ σ) (hστ : σ ≤ τ) :
    let sStar : ℝ := σhat (vStar δ ε) σ τ
    let TStar : ℝ := τ + (ext (vStar δ ε) σ τ).toReal
    (∀ s T : ℝ, 0 ≤ s → s ≤ σ → τ ≤ T →
      Jstar δ ε σ τ ≤ s ^ 2 / T + δ * (σ - s) + ε * (T - τ)) ∧
    (0 ≤ sStar ∧ sStar ≤ σ ∧ τ ≤ TStar ∧ ext (vStar δ ε) σ τ ≠ ∞ ∧
      sStar ^ 2 / TStar + δ * (σ - sStar) + ε * (TStar - τ) = Jstar δ ε σ τ) ∧
    (ε ≠ δ ^ 2 / 4 → ∀ s T : ℝ, 0 ≤ s → s ≤ σ → τ ≤ T →
      s ^ 2 / T + δ * (σ - s) + ε * (T - τ) = Jstar δ ε σ τ → s = sStar ∧ T = TStar) ∧
    (δ ^ 2 / 4 ≤ ε → TStar = τ) ∧
    (ε < δ ^ 2 / 4 → sStar = σ) := by sorry

end GenExactSched
