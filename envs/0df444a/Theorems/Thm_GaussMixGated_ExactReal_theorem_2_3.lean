-- Prove2me | Theorems.Thm_GaussMixGated_ExactReal_theorem_2_3
-- name    : GaussMixGated.ExactReal.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:27:10.036201+00:00
-- url     : https://prove2.me/theorems/92ae54ed-e410-4d3b-af49-696f98722135
-- title:
--   Theorem 2.3 — Posterior mass cover
-- statement:
--   There are constants $C,K>0$ (those of (49)–(50) used by the procedure), universal constants $C_{\mathrm{cov}},C_{\mathrm{rad}}\ge1$, a tolerance $\rho_0>0$, an admissible program and a universal $C'$ with the following property. Let $d,k\ge1$, $\sigma>0$, $F=\nu'*N(0,\sigma^2I_d)$ with $\nu'=\sum_{i<s}w_i\delta_{\mu_i}$ ($s\le k$, $w_i>0$, $\sum w_i=1$), $q$ a probability measure with $D_{\mathrm{KL}}(F\|q)\le e$, $0<\beta,\delta_{\mathrm{cov}}<1$, $0\le b\le1/2$ and $H$ arbitrary. Observations are i.i.d. from $(1-b)F+bH$. Let $Q_y$ be any version of the $q$-posterior for the channel $Y=X+\sigma G$ ($X\sim q$), and let each posterior draw at $y$ be independent with a law $\tilde Q_y$, $\operatorname{TV}(\tilde Q_y,Q_y)\le\rho_0$ for every $y$.
--
--   1. The Section 8 procedure returns
--
--   $$N_{\mathrm{cov}}=\Big\lceil\frac{4k}{\beta}\log\frac{2k}{\delta_{\mathrm{cov}}}\Big\rceil\qquad(5)$$
--
--   centers whose radius-$C_{\mathrm{rad}}\sigma\sqrt{\log(2k/\beta)}$ balls omit at most $3\beta+C_{\mathrm{cov}}e$ of $\nu'$-mass, with probability at least $1-\delta_{\mathrm{cov}}$.
--   2. On every outcome the program computes exactly these centers, makes exactly $N_{\mathrm{cov}}\cdot n$ posterior draws, $n=\lceil C[d\log(2d)+\log(4N_{\mathrm{cov}}/\delta_{\mathrm{cov}})]\rceil$, and halts within $C'(d+k+\beta^{-1}+\log(1/\delta_{\mathrm{cov}})+c_{\mathrm{post}})^{C'}$ work, each posterior draw being charged $c_{\mathrm{post}}+d+1$.
--
--   The cover converts the fitting error into omitted mass with a dimension-free constant.
--
--   Differences from the source:
--   - reading: 'the procedure in Section 8' with constants C, K of (49)–(50) → the explicit §8.4 function with rational C, K > 0 quantified first, plus an admissible program that computes it on every outcome; reason: plan reading 8; rational constants because program literals are rational, and (49)–(50) survive increasing C and K
--   - reading: 'a sufficiently small fixed total-variation error in each independent posterior draw is allowed, by changing universal constants' → ∃ ρ₀ > 0 such that draws of any law within TV ρ₀ of a version of the posterior, uniformly in y, are allowed; reason: the uniform tolerance is the source's 'fixed' error
--   - encoding: the q-posterior → any Markov kernel Q with (law of Y) ⊗ Q = joint law of (Y, X); reason: versions agree F_Y-a.e.; the statement allows every version
--   - encoding: D_KL(F‖q) ≤ e → klDiv F q ≤ ofReal e with 0 ≤ e; reason: e bounds a nonnegative quantity; without 0 ≤ e, ofReal would clip a negative e to 0 and strengthen the conclusion falsely
--   - reading: n = C[d log(2d) + log(4N_cov/δ_cov)] (PDF p. 22) → n = ⌈C[…]⌉; reason: a sample count is an integer
--   - reading: number of posterior samples and arithmetic cost polynomial in d, k, β⁻¹, log(1/δ_cov) and the posterior sampling cost → exactly N_cov · n posterior draws, work ≤ C′·(d + k + β⁻¹ + log(1/δ_cov) + c_post)^C′ on every outcome; reason: deterministic caps (§2.3)
--   - encoding: with probability at least 1 − (failure probability) → a measurable event inside the success set has measure at least 1 − (failure probability); reason: inner-measure form; never applies a measure to a possibly non-measurable set
--   - encoding: operation count of a terminating procedure → nonterminal work plus one terminal accept charge; reason: each executed instruction costs one unit; the halted state remains fixed without repeated charging
--   - generalization: σ ≥ 1 in the §2 preamble → σ > 0 for the posterior-cover theorem; reason: the §8 procedure and proof use only a positive Gaussian scale; this includes every source instance and matches the BRIEF setting
--   - reading: the exact-real model does not specify the set of program literals → witness programs have rational real literals and contain no reject instruction; reason: the uniform finite algorithms use explicit rational constants or larger rational choices of universal constants; this fixes the literal-set ambiguity without advice in real constants, and rejection is encoded by a terminating fallback
-- source:
--   Zheng, Xie, He, Learning Finite Gaussian Location Mixtures via Gated Moments and Posterior Covers, STOC 2027 submission #36 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/36.pdf, PDF p. 6 (printed p. 4), Theorem 2.3, (5); proof §8, PDF pp. 19–22

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_tvDist
import Definitions.Def_GaussMixGated_ExactReal_Machine
import Definitions.Def_GaussMixGated_ExactReal_Mixture
import Definitions.Def_GaussMixGated_ExactReal_Filter

open MeasureTheory ProbabilityTheory InformationTheory

namespace GaussMixGated.ExactReal

/-- Theorem 2.3 (Posterior mass cover) (Zheng–Xie–He, STOC 2027 #36, PDF p. 6). There are
constants `C, K > 0` (those of (49)–(50) used by the procedure), universal constants
`C_cov, C_rad ≥ 1`, a tolerance `ρ₀ > 0`, an admissible program and a universal `C′` such that:
let `F = ν′ ∗ N(0, σ² I_d)` with `ν′` having at most `k` atoms, `D_KL(F‖q) ≤ e`,
`0 < β, δ_cov < 1`, observations from `(1 − b)F + bH`, `b ≤ 1/2`, and independent draws from laws
within total variation `ρ₀` of a version `Q_y` of the `q`-posterior for `Y = X + σG`. Then the
Section 8 procedure returns `N_cov` centers whose radius-`C_rad σ √log(2k/β)` balls omit at most
`3β + C_cov e` of `ν′`-mass, with probability at least `1 − δ_cov`; and the program computes
exactly these centers on every outcome, with exactly `N_cov · n` posterior draws and at most
`C′(d + k + β⁻¹ + log(1/δ_cov) + c_post)^{C′}` work. -/
theorem theorem_2_3 :
    ∃ C K : ℚ, 0 < C ∧ 0 < K ∧ ∃ Ccov Crad ρ₀ : ℝ, 1 ≤ Ccov ∧ 1 ≤ Crad ∧ 0 < ρ₀ ∧
    ∃ Pc : Program, Admissible Pc ∧ ∃ C' : ℕ,
    ∀ (d k : ℕ), 1 ≤ d → 1 ≤ k →
    ∀ (σ β δ e b : ℝ), 0 < σ → 0 < β → β < 1 → 0 < δ → δ < 1 → 0 ≤ e → 0 ≤ b → b ≤ 1 / 2 →
    ∀ (s : ℕ) (w : Fin s → ℝ) (μ : Fin s → EuclideanSpace ℝ (Fin d)), IsMixingMeasure k s w →
    ∀ (q H : Measure (EuclideanSpace ℝ (Fin d))), IsProbabilityMeasure q →
      IsProbabilityMeasure H → klDiv (mixtureLaw d s σ w μ) q ≤ ENNReal.ofReal e →
    ∀ (Qpost : Kernel (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d))),
      IsMarkovKernel Qpost →
      (q.prod (stdGaussian (EuclideanSpace ℝ (Fin d)))).map (fun p => (p.1 + σ • p.2, p.1)) =
        ((q.prod (stdGaussian (EuclideanSpace ℝ (Fin d)))).map (fun p => p.1 + σ • p.2)) ⊗ₘ
          Qpost →
    ∀ (Ω : Type) [MeasurableSpace Ω] (lam : Measure Ω), IsProbabilityMeasure lam →
    ∀ (resp : EuclideanSpace ℝ (Fin d) → Ω → EuclideanSpace ℝ (Fin d)),
      Measurable (Function.uncurry resp) →
      (∀ y, FoundationsRL.DECLower.tvDist (lam.map (resp y)) (Qpost y) ≤ ρ₀) →
    ∀ cpost : ℕ,
      (∃ E : Set ((ℕ → EuclideanSpace ℝ (Fin d)) × (ℕ → ℝ) × (ℕ → Ω)), MeasurableSet E ∧
        (∀ ω ∈ E, omittedMass w μ
            (coverCenters C K d k σ β δ ω.1 ω.2.1 (fun j y => resp y (ω.2.2 j)))
            (Crad * σ * Real.sqrt (Real.log (2 * k / β))) ≤ 3 * β + Ccov * e) ∧
        ENNReal.ofReal (1 - δ) ≤
          ((iidTape (contaminated b (mixtureLaw d s σ w μ) H)).prod
            (gaussTape.prod (iidTape lam))) E) ∧
      (∀ (obs : ℕ → EuclideanSpace ℝ (Fin d)) (g : ℕ → ℝ) (ω : ℕ → Ω),
        HaltsWithin Pc ⟨g, [obsChannel obs, kernelChannel resp cpost ω]⟩ (coverStart d k σ β δ)
          (C' * ((d : ℝ) + k + β⁻¹ + Real.log (1 / δ) + cpost) ^ C') ∧
        (final Pc ⟨g, [obsChannel obs, kernelChannel resp cpost ω]⟩
            (coverStart d k σ β δ)).calls 1 = Ncov k β δ * coverBatch C d k β δ ∧
        ∀ (t : Fin (Ncov k β δ)) (i : Fin d),
          (final Pc ⟨g, [obsChannel obs, kernelChannel resp cpost ω]⟩
              (coverStart d k σ β δ)).mem ((t : ℕ) * d + i) =
            coverCenters C K d k σ β δ obs g (fun j y => resp y (ω j)) t i) := by sorry

end GaussMixGated.ExactReal
