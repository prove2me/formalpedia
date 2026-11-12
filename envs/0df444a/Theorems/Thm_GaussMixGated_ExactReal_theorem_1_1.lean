-- Prove2me | Theorems.Thm_GaussMixGated_ExactReal_theorem_1_1
-- name    : GaussMixGated.ExactReal.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:25:51.750297+00:00
-- url     : https://prove2.me/theorems/e5c79e53-111e-40a9-a8ab-25ecee3ec4bd
-- title:
--   Theorem 1.1 — Exact-real distribution learning
-- statement:
--   There are one admissible trainer program $T$, one admissible oracle-free sampler program $S$ and one universal $C\in\mathbb N$ such that the following holds for all $d,k\ge1$, all $0<\varepsilon,\delta<1/4$ and every mixture
--
--   $$P=\nu*N(0,I_d),\qquad\nu=\sum_{i=1}^sw_i\delta_{\mu_i},\quad s\le k,\ w_i>0,\ \sum_iw_i=1,\ \mu_i\in\mathbb R^d,$$
--
--   with arbitrary (possibly coincident) means. Put $P_*=2+d+k+\varepsilon^{-1}+\log(1/\delta)$. The trainer reads $d,k,\varepsilon,\delta$ and i.i.d. samples from $P$, and may draw standard Gaussians.
--
--   1. On every sample tape and every Gaussian tape the trainer halts within $C\,P_*^{C}$ units of work; each sample costs $d+1$ units, so it uses at most $C\,P_*^{C}$ samples.
--   2. Its description cells plus the fixed sampler instructions total at most $C\,P_*^{C}$.
--   3. On every training outcome, the sampler run on that description halts within $C\,P_*^{C}$ units of work on every Gaussian tape.
--   4. With probability at least $1-\delta$ over training, the law $\hat P$ of a single output of the sampler satisfies
--
--   $$\operatorname{TV}(P,\hat P)\le\varepsilon.$$
--
--   This is polynomial-time total-variation learning of finite Gaussian location mixtures with no restriction on the means or the weights, in the exact-real model of the paper. The output map on every produced description is measurable, so its pushforward of the Gaussian tape is a probability law. The output law need not be a Gaussian mixture.
--
--   Differences from the source:
--   - reading: 'there is an algorithm' with poly(d, k, ε⁻¹, log(1/δ)) bounds whose exponents are universal → one fixed trainer and one fixed sampler program and one C ∈ ℕ, chosen before d, k, ε, δ, ν; every bound is C·P*^C with P* = 2 + d + k + ε⁻¹ + log(1/δ); reason: a uniform algorithm (plan reading 1); P* is §2.3's own parameter and C·P*^C is equivalent to poly(·) with universal exponents for d, k ≥ 1, ε, δ < 1/4 (reading 2)
--   - reading: sample count, operation count, description size and per-output operation count bounded → bounded on every sample tape and every Gaussian tape; reason: PDF p. 3: 'every loop has a prescribed finite cap, including on unsuccessful training outcomes'; §2.3 'on every outcome' (reading 3)
--   - encoding: the exact-real model (real arithmetic, comparisons, square roots, exponentials, logarithms, ideal Gaussian draws) → the published real-RAM core extended with sqrt, exp, log, a Gaussian-tape draw and a sample channel; one unit per instruction, including one terminal accept charge, d + 1 per sample; rational literals and no reject (admissible); reason: rational literals exclude advice hidden in constants (reading 4); Lean's x/0 = 0, log x = log|x|, √x = 0 for x < 0 give no information a sign test does not
--   - reading: 'returns a finite randomized sampling program' with real-register description size → a fixed sampler program run on the trainer's output cells; size = number of cells (plus |S|); reason: equivalent up to polynomial overhead to emitting instructions, which a fixed interpreter can execute (reading 5)
--   - encoding: TV(P, P̂) → the published tvDist (supremum over measurable sets) between probability measures on EuclideanSpace ℝ (Fin d); measurability of the sampler output map on every produced description is a conclusion; reason: the law of a randomized output is a probability measure; explicit measurability prevents the zero-map convention for nonmeasurable functions
--   - encoding: with probability at least 1 − (failure probability) → a measurable event inside the success set has measure at least 1 − (failure probability); reason: inner-measure form; never applies a measure to a possibly non-measurable set
--   - encoding: a finite output description → pointer register 0 at halting is nonnegative and holds the number of description cells; reason: ensures that converting the integer length to a natural number is exact
-- source:
--   Zheng, Xie, He, Learning Finite Gaussian Location Mixtures via Gated Moments and Posterior Covers, STOC 2027 submission #36 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/36.pdf, PDF p. 3 (printed p. 1), Theorem 1.1, with the model paragraph; proof §2.1–2.3, PDF pp. 7–8

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_tvDist
import Definitions.Def_GaussMixGated_ExactReal_Machine
import Definitions.Def_GaussMixGated_ExactReal_Mixture

open MeasureTheory

namespace GaussMixGated.ExactReal

/-- Theorem 1.1 (Exact-real distribution learning) (Zheng–Xie–He, STOC 2027 #36, PDF p. 3).
There are one admissible trainer program `T`, one admissible oracle-free sampler program `S` and
one universal exponent `C` such that, for all `d, k ≥ 1`, `0 < ε, δ < 1/4` and every mixture
`P = ν ∗ N(0, I_d)`, `ν = ∑_{i<s} w_i δ_{μ_i}`, `s ≤ k`, `w_i > 0`, `∑ w_i = 1`, with
`P* = 2 + d + k + ε⁻¹ + log(1/δ)`:
1. on every sample tape and every Gaussian tape the trainer halts within `C·P*^C` work (each
   sample costs `d + 1` units, so the number of samples is bounded too);
2. its output description cells plus the fixed sampler's instructions total at most `C·P*^C`;
3. on every training outcome, the sampler run on that description halts within `C·P*^C` work on
   every Gaussian tape;
4. each output map is measurable, and with probability at least `1 − δ` over training,
   `TV(P, P̂) ≤ ε` for the law `P̂` of one output. -/
theorem theorem_1_1 :
    ∃ T S : Program, Admissible T ∧ Admissible S ∧ OracleFree S ∧ ∃ C : ℕ,
    ∀ (d k : ℕ), 1 ≤ d → 1 ≤ k →
    ∀ (ε δ : ℝ), 0 < ε → ε < 1 / 4 → 0 < δ → δ < 1 / 4 →
    ∀ (s : ℕ) (w : Fin s → ℝ) (μ : Fin s → EuclideanSpace ℝ (Fin d)), IsMixingMeasure k s w →
      (∀ (xs : ℕ → EuclideanSpace ℝ (Fin d)) (g : ℕ → ℝ),
        HaltsWithin T (trainerEnv xs g) (trainerStart d k ε δ)
          (C * (2 + (d : ℝ) + k + ε⁻¹ + Real.log (1 / δ)) ^ C) ∧
        0 ≤ (trainerFinal T d k ε δ xs g).ptrs 0 ∧
        ((descLen (trainerFinal T d k ε δ xs g) + S.length : ℕ) : ℝ) ≤
          C * (2 + (d : ℝ) + k + ε⁻¹ + Real.log (1 / δ)) ^ C ∧
        Measurable (samplerOut d S (desc (trainerFinal T d k ε δ xs g))) ∧
        ∀ g' : ℕ → ℝ,
          HaltsWithin S (samplerEnv g') (samplerStart (desc (trainerFinal T d k ε δ xs g)))
            (C * (2 + (d : ℝ) + k + ε⁻¹ + Real.log (1 / δ)) ^ C)) ∧
      ∃ E : Set ((ℕ → EuclideanSpace ℝ (Fin d)) × (ℕ → ℝ)), MeasurableSet E ∧
        (∀ ω ∈ E, FoundationsRL.DECLower.tvDist (mixtureLaw d s 1 w μ)
            (samplerLaw d S (desc (trainerFinal T d k ε δ ω.1 ω.2))) ≤ ε) ∧
        ENNReal.ofReal (1 - δ) ≤ ((iidTape (mixtureLaw d s 1 w μ)).prod gaussTape) E := by sorry

end GaussMixGated.ExactReal
