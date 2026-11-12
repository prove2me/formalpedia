-- Prove2me | Theorems.Thm_GaussMixGated_ExactReal_theorem_2_2
-- name    : GaussMixGated.ExactReal.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:26:48.069316+00:00
-- url     : https://prove2.me/theorems/da87bba4-c500-4c53-937b-f5c3a68e3e28
-- title:
--   Theorem 2.2 — Fitting with linear omitted-mass loss
-- statement:
--   There are an admissible program and a universal $C$ with the following property. Let $Q=\frac1m\sum_jN(c_j,\sigma^2I_d)$ ($m\ge1$, $\sigma\ge1$) and a measurable feature map $z:\mathbb R^d\to\mathbb R^N$ with $z_0\equiv1$ and $\|z(x)\|\le L_z$ be fixed. Let $F$ be a probability measure with $F\ll Q$, $H$ an arbitrary probability measure, $0\le b\le1/2$ and $P'=(1-b)F+bH$. Let $0<a\le1$, $\kappa=a/64$, $0\le\theta\le a\sqrt\kappa/64$, $0<\delta'<1$, and suppose (2): some $S\succeq0$ with $\operatorname{tr}S\le1$ has $\|z^{\top}Sz-dF/dQ\|_{L^2(Q)}\le\theta$. The procedure reads $N,L_z,a,\delta'$, values $z(X)$ for fresh $X\sim Q$ and values $z(X)$ for fresh $X\sim P'$.
--
--   1. On every outcome it halts within $C(N+L_z+a^{-1}+\log(1/\delta'))^C$ work and returns $C\succeq0$ with $\operatorname{tr}C\le4$; hence $f=\kappa+z^{\top}Cz$ satisfies $\kappa\le f\le\kappa+4L_z^2$.
--   2. With probability at least $1-\delta'$, $q=Qf/Z$, $Z=\mathbb E_Qf$, satisfies
--
--   $$D_{\mathrm{KL}}(F\|q)\le-\log(1-b)+a,$$
--
--   and $-\log(1-b)+a\le2b+a$.
--
--   The omitted mass $b$ enters the fitting error linearly, which keeps the scale recursion of §2.2 polynomial.
--
--   Differences from the source:
--   - generalization: F the normalized covered submixture and z the dictionary of Theorem 2.1 → any probability measure F ≪ Q and any measurable z with z₀ ≡ 1 and ‖z‖ ≤ L_z; reason: §6 uses only g = dF/dQ ∈ L²(Q) and these properties of z; the source's F and z satisfy them
--   - encoding: (2) holds (a statement about the density F/Q) → F ≪ Q together with the eLpNorm bound for the Radon–Nikodym derivative; reason: without F ≪ Q, rnDeriv drops a singular part and (4) would be false; part of what (2) means
--   - reading: costs polynomial in N, L_z, a⁻¹ and log inverse failure probability → the procedure accesses z only through the oracles z(X), X ∼ Q and X ∼ P′, each call charged 1 + N; work ≤ C·(N + L_z + a⁻¹ + log(1/δ′))^C; reason: this is why d and m do not appear; γ, r₀, u, ε_R of (3) are internal parameters
--   - encoding: with probability at least 1 − (failure probability) → a measurable event inside the success set has measure at least 1 − (failure probability); reason: inner-measure form; never applies a measure to a possibly non-measurable set
--   - encoding: the L² approximation tolerance θ → 0 ≤ θ, with the L² error compared to ENNReal.ofReal θ; reason: a norm tolerance is nonnegative; the guard prevents ofReal from turning a negative tolerance into zero
--   - encoding: operation count of a terminating procedure → nonterminal work plus one terminal accept charge; reason: each executed instruction costs one unit; the halted state remains fixed without repeated charging
--   - reading: the exact-real model does not specify the set of program literals → witness programs have rational real literals and contain no reject instruction; reason: the uniform finite algorithms use explicit rational constants or larger rational choices of universal constants; this fixes the literal-set ambiguity without advice in real constants, and rejection is encoded by a terminating fallback
-- source:
--   Zheng, Xie, He, Learning Finite Gaussian Location Mixtures via Gated Moments and Posterior Covers, STOC 2027 submission #36 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/36.pdf, PDF p. 6 (printed p. 4), Theorem 2.2, (3)–(4); proof §6, PDF pp. 15–18 (printed pp. 13–16)

import Mathlib
import Definitions.Def_GaussMixGated_ExactReal_Machine
import Definitions.Def_GaussMixGated_ExactReal_Mixture
import Definitions.Def_GaussMixGated_ExactReal_Procedures

open MeasureTheory InformationTheory

namespace GaussMixGated.ExactReal

/-- Theorem 2.2 (Fitting with linear omitted-mass loss) (Zheng–Xie–He, STOC 2027 #36, PDF p. 6).
There are an admissible program `Pc` and a universal `C` such that: let
`Q = (1/m) ∑_j N(c_j, σ² I_d)` and a measurable feature map `z : ℝ^d → ℝ^N` with `z₀ ≡ 1` and
`‖z‖ ≤ L_z` be fixed, let `P′ = (1 − b)F + bH` with `0 ≤ b ≤ 1/2`, `F ≪ Q`, `H` arbitrary, and
suppose (2) holds with `θ ≤ a√κ/64`, `κ = a/64`, `0 < a ≤ 1`. Reading `z(X)` for fresh `X ∼ Q`
and for fresh `X ∼ P′`, `Pc` halts within `C·(N + L_z + a⁻¹ + log(1/δ′))^C` work with a matrix
`C ⪰ 0`, `tr C ≤ 4`, so `κ ≤ f ≤ κ + 4L_z²` for `f = κ + zᵀCz`, on every outcome; and with
probability at least `1 − δ′`, `q = Qf/Z` satisfies `D_KL(F‖q) ≤ −log(1 − b) + a`; moreover
`−log(1 − b) + a ≤ 2b + a`. -/
theorem theorem_2_2 :
    ∃ Pc : Program, Admissible Pc ∧ ∃ C : ℕ,
    ∀ (d m N : ℕ), 1 ≤ d → 1 ≤ m → ∀ hN : 1 ≤ N,
    ∀ (c : Fin m → EuclideanSpace ℝ (Fin d)) (σ : ℝ), 1 ≤ σ →
    ∀ (z : EuclideanSpace ℝ (Fin d) → Fin N → ℝ), Measurable z →
    ∀ Lz : ℝ, (∀ x, z x ⟨0, hN⟩ = 1) → (∀ x, Real.sqrt (∑ i, z x i ^ 2) ≤ Lz) →
    ∀ (a δ' : ℝ), 0 < a → a ≤ 1 → 0 < δ' → δ' < 1 →
    ∀ (F H : Measure (EuclideanSpace ℝ (Fin d))), IsProbabilityMeasure F →
      IsProbabilityMeasure H → F ≪ centerMixture σ c →
    ∀ b : ℝ, 0 ≤ b → b ≤ 1 / 2 →
    ∀ θ : ℝ, 0 ≤ θ → θ ≤ a * Real.sqrt (a / 64) / 64 →
      (∃ S : Matrix (Fin N) (Fin N) ℝ, S.PosSemidef ∧ S.trace ≤ 1 ∧
        eLpNorm (fun x => (∑ i, ∑ j, S i j * z x i * z x j) -
            (F.rnDeriv (centerMixture σ c) x).toReal) 2 (centerMixture σ c) ≤
          ENNReal.ofReal θ) →
      (∀ (xq xp : ℕ → EuclideanSpace ℝ (Fin d)) (g : ℕ → ℝ),
        HaltsWithin Pc (fitEnv z xq xp g) (fitStart N Lz a δ')
          (C * ((N : ℝ) + Lz + a⁻¹ + Real.log (1 / δ')) ^ C) ∧
        (fitMatrix N (final Pc (fitEnv z xq xp g) (fitStart N Lz a δ'))).PosSemidef ∧
        (fitMatrix N (final Pc (fitEnv z xq xp g) (fitStart N Lz a δ'))).trace ≤ 4 ∧
        ∀ x, a / 64 ≤
            fitNumerator (a / 64) (fitMatrix N (final Pc (fitEnv z xq xp g) (fitStart N Lz a δ')))
              z x ∧
          fitNumerator (a / 64) (fitMatrix N (final Pc (fitEnv z xq xp g) (fitStart N Lz a δ')))
              z x ≤ a / 64 + 4 * Lz ^ 2) ∧
      (∃ E : Set ((ℕ → EuclideanSpace ℝ (Fin d)) × (ℕ → EuclideanSpace ℝ (Fin d)) × (ℕ → ℝ)),
        MeasurableSet E ∧
        (∀ ω ∈ E, klDiv F (fittedLaw (centerMixture σ c)
            (fitNumerator (a / 64)
              (fitMatrix N (final Pc (fitEnv z ω.1 ω.2.1 ω.2.2) (fitStart N Lz a δ'))) z)) ≤
          ENNReal.ofReal (-Real.log (1 - b) + a)) ∧
        ENNReal.ofReal (1 - δ') ≤
          ((iidTape (centerMixture σ c)).prod
            ((iidTape (contaminated b F H)).prod gaussTape)) E) ∧
      -Real.log (1 - b) + a ≤ 2 * b + a := by sorry

end GaussMixGated.ExactReal
