-- Prove2me | Theorems.Thm_MaxSpectralRisk_Duality_proposition_2
-- name    : MaxSpectralRisk.Duality.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:22.308582+00:00
-- url     : https://prove2.me/theorems/45874514-fba0-40b9-9613-7d48ff2becb4
-- title:
--   Proposition 2, p. 10 — H(·, β) is affine and (for β ∈ L¹(γσ)) upper semicontinuous in π; H(π, ·) is convex and D_H is convex
-- statement:
--   Throughout, $\mathcal X$ and $\mathcal Y$ are Polish spaces with their Borel $\sigma$-algebras, $\mu$ and $\nu$ are Borel probability measures on them, $\Pi(\mu,\nu)$ is the set of couplings, $\sigma$ is a bounded, right-continuous spectral function (A.4), and $L:\mathcal X\times\mathcal Y\to\mathbb R$ is the loss. Assume A.1–A.3, and let $H(\pi,\beta)=\int_0^1\beta(u)+(1-u)^{-1}\mathbb E_\pi[(L-\beta(u))_+]\,d\Gamma_\sigma(u)\in\mathbb R\cup\{\infty\}$ and $\mathcal D_H=\{\beta\in\mathcal L^1(\Gamma_\sigma):H(\pi,\beta)<\infty\ \forall\pi\in\Pi(\mu,\nu)\}$.
--
--   1. For $\beta\in\mathcal D_H$, $\pi_0,\pi_1\in\Pi(\mu,\nu)$ and $\lambda\in(0,1)$,
--   $$H(\lambda\pi_1+(1-\lambda)\pi_0,\beta)=\lambda H(\pi_1,\beta)+(1-\lambda)H(\pi_0,\beta);$$
--   in particular $H(\cdot,\beta)$ is concave in $\pi$.
--   2. If $\beta\in\mathcal L^1(\gamma_\sigma)$ and couplings $\pi_n\to\pi$ weakly, all in $\Pi(\mu,\nu)$, then $\limsup_n H(\pi_n,\beta)\le H(\pi,\beta)$.
--   3. For fixed $\pi\in\Pi(\mu,\nu)$, $H(\pi,\cdot)$ is convex on $\mathcal L^1(\Gamma_\sigma)$, and therefore $\mathcal D_H$ is a convex set.
--
--   These are the concavity, upper semicontinuity and convexity hypotheses of the minimax theorem behind Proposition 3.
--
--   **Formalization Note.** Values are in the extended reals; convexity of $H(\pi,\cdot)$ is the inequality $H(\pi,\lambda\beta_1+(1-\lambda)\beta_0)\le\lambda H(\pi,\beta_1)+(1-\lambda)H(\pi,\beta_0)$ for $\beta_0,\beta_1\in\mathcal L^1(\Gamma_\sigma)$. Weak (narrow) convergence is convergence in Mathlib's `ProbabilityMeasure` topology.
-- source:
--   Ghossoub, Hall, Saunders, Maximum Spectral Measures of Risk with given Risk Factor Marginal Distributions, arXiv:2010.14673v1, p. 10, Proposition 2 (with the definitions of H and D_H on p. 10)

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_MaxSpectralRisk_Duality_Setting

namespace MaxSpectralRisk.Duality

open MeasureTheory Filter Topology

theorem proposition_2 {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (sig : SpectralFunction) (L : X × Y → ℝ)
    (hA : Assumptions L μ ν) :
    (∀ β ∈ DH sig L μ ν, ∀ π₀ ∈ MongeKantorovichYao.transferencePlans μ ν, ∀ π₁ ∈ MongeKantorovichYao.transferencePlans μ ν,
      ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        H sig L (ENNReal.ofReal t • π₁ + ENNReal.ofReal (1 - t) • π₀) β =
          ((t : ℝ) : EReal) * H sig L π₁ β + ((1 - t : ℝ) : EReal) * H sig L π₀ β) ∧
    (∀ β : ℝ → ℝ, Integrable β (gam sig) →
      ∀ (πs : ℕ → ProbabilityMeasure (X × Y)) (π : ProbabilityMeasure (X × Y)),
        (∀ n, (πs n : Measure (X × Y)) ∈ MongeKantorovichYao.transferencePlans μ ν) →
        (π : Measure (X × Y)) ∈ MongeKantorovichYao.transferencePlans μ ν →
        Tendsto πs atTop (𝓝 π) →
        limsup (fun n => H sig L (πs n : Measure (X × Y)) β) atTop ≤
          H sig L (π : Measure (X × Y)) β) ∧
    (∀ π ∈ MongeKantorovichYao.transferencePlans μ ν, ∀ β₀ β₁ : ℝ → ℝ,
      Integrable β₀ (Gam sig) → Integrable β₁ (Gam sig) → ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        H sig L π (t • β₁ + (1 - t) • β₀) ≤
          ((t : ℝ) : EReal) * H sig L π β₁ + ((1 - t : ℝ) : EReal) * H sig L π β₀) ∧
    Convex ℝ (DH sig L μ ν) := by sorry

end MaxSpectralRisk.Duality
