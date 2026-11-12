-- Prove2me | Theorems.Thm_GaussMixGated_ExactReal_theorem_2_1
-- name    : GaussMixGated.ExactReal.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:26:44.663449+00:00
-- url     : https://prove2.me/theorems/bb22e1a6-e557-40e1-9f4f-7fd2ac220828
-- title:
--   Theorem 2.1 — Partial-cover dictionary
-- statement:
--   There are an admissible construction program, an admissible deterministic feature evaluator and a universal $C$ with the following property. Let $d,k,m\ge1$, centers $c_1,\dots,c_m\in\mathbb R^d$, $\sigma\ge1$, a radius $r$, $0<\theta<1/4$, $0<\delta'<1$, and a mixing measure $\nu=\sum_{i<s}w_i\delta_{\mu_i}$ ($s\le k$, $w_i>0$, $\sum w_i=1$) such that the atoms within $r$ of some center have total weight at least $1/2$. The construction reads $d,k,m$, the centers, $\sigma,r,\theta,\delta'$ and draws from $P_\sigma=\nu*N(0,\sigma^2I_d)$. Put $P=d+k+m+\theta^{-1}+\exp((r/\sigma)^2)+\log(1/\delta')$ and $Q=\frac1m\sum_jN(c_j,\sigma^2I_d)$.
--
--   1. On every outcome the construction halts within $C\,P^C$ work with a description of at most $C\,P^C$ cells, a feature dimension $1\le N\le C\,P^C$ and a bound $L_z\le C\,P^C$; for every $x$ the evaluator computes $z(x)\in\mathbb R^N$ within $C\,P^C$ work, $z_0(x)=1$ and $\|z(x)\|\le L_z$.
--   2. With probability at least $1-\delta'$ there is $S\succeq0$ with $\operatorname{tr}S\le1$ and
--
--   $$\big\|z^{\top}Sz-dF/dQ\big\|_{L^2(Q)}\le\theta,\qquad(2)$$
--
--   where $F$ is the normalized submixture of all covered atoms.
--
--   The matrix $S$ is used only in the analysis. The dictionary represents the square-root density of the covered part of the mixture.
--
--   Differences from the source:
--   - reading: 'a finite sample-based procedure constructs Q, z' with stored circuits → an admissible program with a P_σ-draw channel and Gaussian tape, outputting a description, N and L_z; z is computed by a fixed deterministic evaluator program; reason: makes 'procedure' and 'stored circuits' statements about the defined machine
--   - reading: centers cover at least 1 − b of the latent mass within radius r, b ≤ 1/2; F the normalized submixture of all covered atoms → covered mass ≥ 1/2, F over all covered atoms; reason: §5.1 sets s = Σ_covered w_i = 1 − b ≥ 1/2
--   - reading: polynomial in d, k, m, θ⁻¹, exp(O((r/σ)²)) and log inverse failure probability → ≤ C·(d + k + m + θ⁻¹ + exp((r/σ)²) + log(1/δ′))^C on every outcome; reason: exp(O(x)) folds into exp(x)^C
--   - encoding: F/Q and the L²(Q) norm → Radon–Nikodym derivative dF/dQ and eLpNorm · 2 Q; reason: Lean convention; F ≪ Q for Gaussians
--   - encoding: with probability at least 1 − (failure probability) → a measurable event inside the success set has measure at least 1 − (failure probability); reason: inner-measure form; never applies a measure to a possibly non-measurable set
--   - encoding: operation count of a terminating procedure → nonterminal work plus one terminal accept charge; reason: each executed instruction costs one unit; the halted state remains fixed without repeated charging
--   - encoding: a finite output description → pointer register 0 at halting is nonnegative and holds the number of description cells; reason: ensures that converting the integer length to a natural number is exact
--   - reading: the exact-real model does not specify the set of program literals → witness programs have rational real literals and contain no reject instruction; reason: the uniform finite algorithms use explicit rational constants or larger rational choices of universal constants; this fixes the literal-set ambiguity without advice in real constants, and rejection is encoded by a terminating fallback
-- source:
--   Zheng, Xie, He, Learning Finite Gaussian Location Mixtures via Gated Moments and Posterior Covers, STOC 2027 submission #36 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/36.pdf, PDF p. 6 (printed p. 4), Theorem 2.1, (2); proof §5, PDF pp. 13–15

import Mathlib
import Definitions.Def_GaussMixGated_ExactReal_Machine
import Definitions.Def_GaussMixGated_ExactReal_Mixture
import Definitions.Def_GaussMixGated_ExactReal_Procedures

open MeasureTheory

namespace GaussMixGated.ExactReal

/-- Theorem 2.1 (Partial-cover dictionary) (Zheng–Xie–He, STOC 2027 #36, PDF p. 6). There are an
admissible construction program `Pc`, an admissible deterministic feature evaluator `Ev` and a
universal `C` such that: given `m ≥ 1` centers that cover at least half of the latent mass within
radius `r`, `σ ≥ 1`, `0 < θ < 1/4` and `0 < δ′ < 1`, and draws from `P_σ`, on every outcome
`Pc` halts within `C·P^C` work, `P = d + k + m + θ⁻¹ + exp((r/σ)²) + log(1/δ′)`, with a
description, a feature dimension `N ≥ 1` and a norm bound `L_z`, all at most `C·P^C`; the
features `z(x)` computed by `Ev` (within `C·P^C` work for every `x`) satisfy `z₀ ≡ 1` and
`‖z(x)‖ ≤ L_z`; and with probability at least `1 − δ′` there is `S ⪰ 0`, `tr S ≤ 1`, with
`‖zᵀSz − dF/dQ‖_{L²(Q)} ≤ θ`, `F` the normalized submixture of all covered atoms and
`Q = (1/m) ∑_j N(c_j, σ² I_d)`. -/
theorem theorem_2_1 :
    ∃ Pc Ev : Program, Admissible Pc ∧ Admissible Ev ∧ OracleFree Ev ∧ GaussFree Ev ∧
    ∃ C : ℕ,
    ∀ (d k m : ℕ), 1 ≤ d → 1 ≤ k → 1 ≤ m →
    ∀ (c : Fin m → EuclideanSpace ℝ (Fin d)) (σ r θ δ' : ℝ), 1 ≤ σ → 0 < θ → θ < 1 / 4 →
      0 < δ' → δ' < 1 →
    ∀ (s : ℕ) (w : Fin s → ℝ) (μ : Fin s → EuclideanSpace ℝ (Fin d)), IsMixingMeasure k s w →
      1 / 2 ≤ coveredMass w μ c r →
      (∀ (xs : ℕ → EuclideanSpace ℝ (Fin d)) (g : ℕ → ℝ),
        HaltsWithin Pc (dictionaryEnv xs g) (dictionaryStart k c σ r θ δ')
          (C * ((d : ℝ) + k + m + θ⁻¹ + Real.exp ((r / σ) ^ 2) + Real.log (1 / δ')) ^ C) ∧
        0 ≤ (final Pc (dictionaryEnv xs g) (dictionaryStart k c σ r θ δ')).ptrs 0 ∧
        (descLen (final Pc (dictionaryEnv xs g) (dictionaryStart k c σ r θ δ')) : ℝ) ≤
          C * ((d : ℝ) + k + m + θ⁻¹ + Real.exp ((r / σ) ^ 2) + Real.log (1 / δ')) ^ C ∧
        1 ≤ featureDim (final Pc (dictionaryEnv xs g) (dictionaryStart k c σ r θ δ')) ∧
        (featureDim (final Pc (dictionaryEnv xs g) (dictionaryStart k c σ r θ δ')) : ℝ) ≤
          C * ((d : ℝ) + k + m + θ⁻¹ + Real.exp ((r / σ) ^ 2) + Real.log (1 / δ')) ^ C ∧
        featureBound (final Pc (dictionaryEnv xs g) (dictionaryStart k c σ r θ δ')) ≤
          C * ((d : ℝ) + k + m + θ⁻¹ + Real.exp ((r / σ) ^ 2) + Real.log (1 / δ')) ^ C ∧
        ∀ x : EuclideanSpace ℝ (Fin d),
          HaltsWithin Ev (samplerEnv (fun _ => 0))
            (featureStart (desc (final Pc (dictionaryEnv xs g) (dictionaryStart k c σ r θ δ'))) x)
            (C * ((d : ℝ) + k + m + θ⁻¹ + Real.exp ((r / σ) ^ 2) + Real.log (1 / δ')) ^ C) ∧
          featureValue Ev (desc (final Pc (dictionaryEnv xs g) (dictionaryStart k c σ r θ δ'))) x 0
            = 1 ∧
          Real.sqrt (∑ i ∈ Finset.range
              (featureDim (final Pc (dictionaryEnv xs g) (dictionaryStart k c σ r θ δ'))),
            featureValue Ev (desc (final Pc (dictionaryEnv xs g)
              (dictionaryStart k c σ r θ δ'))) x i ^ 2) ≤
            featureBound (final Pc (dictionaryEnv xs g) (dictionaryStart k c σ r θ δ'))) ∧
      ∃ E : Set ((ℕ → EuclideanSpace ℝ (Fin d)) × (ℕ → ℝ)), MeasurableSet E ∧
        (∀ ω ∈ E, ∃ S : Matrix
            (Fin (featureDim (final Pc (dictionaryEnv ω.1 ω.2) (dictionaryStart k c σ r θ δ'))))
            (Fin (featureDim (final Pc (dictionaryEnv ω.1 ω.2) (dictionaryStart k c σ r θ δ'))))
            ℝ,
          S.PosSemidef ∧ S.trace ≤ 1 ∧
          eLpNorm (fun x => matQuad S (featureValue Ev
              (desc (final Pc (dictionaryEnv ω.1 ω.2) (dictionaryStart k c σ r θ δ'))) x) -
              ((coveredSubmixture σ w μ c r).rnDeriv (centerMixture σ c) x).toReal)
            2 (centerMixture σ c) ≤ ENNReal.ofReal θ) ∧
        ENNReal.ofReal (1 - δ') ≤ ((iidTape (mixtureLaw d s σ w μ)).prod gaussTape) E := by sorry

end GaussMixGated.ExactReal
