-- Prove2me | Theorems.Thm_GaussMixHH_fact_11
-- name    : GaussMixHH.fact_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:07.21058+00:00
-- url     : https://prove2.me/theorems/3a05b9bb-37fb-40e8-81a0-393d5c733938
-- title:
--   Fact 11, p.17 — subharmonic comparison $g(a)\le\int_{\partial D}g\,P_{D,a}\,d\sigma$
-- statement:
--   Let $D=D(c,R)$ be an open disk in $\mathbb C$ ($R>0$), $\sigma$ normalized arclength on $\partial D$, and $P_{D,a}(\zeta)=(R^2-|a-c|^2)/|\zeta-a|^2$ the Poisson kernel. Let $g$ be real valued and continuous on $\overline D$, twice continuously differentiable on $D$, with $\Delta g\ge0$ throughout $D$. Then:
--
--   1. for every $a\in D$,
--   $$g(a)\le\int_{\partial D}g(\zeta)P_{D,a}(\zeta)\,d\sigma(\zeta);$$
--   2. if $H$ is harmonic on $D$, continuous on $\overline D$, and $g\le H$ on $\partial D$, then $g\le H$ throughout $D$.
--
--   The paper applies the first part to $\log|\Psi|$ on the observation disk (via a smoothing) to force a set of boundary points of controlled harmonic measure where $|\Psi|$ is large (Lemma 15).
--
--   **Formalization Note** $\int_{\partial D}\cdot\,d\sigma$ is Mathlib's `circleAverage`, $P_{D,a}$ is Mathlib's `poissonKernel`, $\Delta$ is Mathlib's Laplacian on $\mathbb C\cong\mathbb R^2$, and "harmonic on $D$" is `HarmonicOnNhd`.
--
--   Differences from the source:
--   - encoding: ∫_{∂D} · dσ, P_{D,a}, ∆, "harmonic on D" → Real.circleAverage, poissonKernel, Mathlib's Laplacian on ℂ, HarmonicOnNhd; reason: the same objects in Mathlib's normalization (checked: poissonKernel c a ζ = (R² − |a − c|²)/|ζ − a|² on the circle)
-- source:
--   De, Huang, Nadimpalli, Servedio, Optimally learning mixtures of arbitrarily many Gaussians, STOC 2027 submission (manuscript sha256 4f36a53e…), Fact 11, p.17 (PDF p.19), citing [Ahl79, Ch. 6, §4.1]; Poisson kernel from Fact 10, p.17

import Mathlib

open Complex Metric Laplacian InnerProductSpace

namespace GaussMixHH

/-- **Fact 11** (Subharmonic comparison).

A. De, Y. Huang, S. Nadimpalli, R. A. Servedio, *Optimally learning mixtures of arbitrarily many
Gaussians*, STOC 2027 submission (manuscript sha256 4f36a53e…), Fact 11, p.17 (PDF p.19), citing
[Ahl79, Chapter 6, Section 4.1]; the Poisson kernel and `σ` are from Fact 10 and p.16.

"Let g be real-valued and continuous on D̄, twice continuously differentiable on D, and satisfy
∆g ≥ 0 throughout D. Then, for every a ∈ D, g(a) ≤ ∫_{∂D} g(ζ)P_{D,a}(ζ) dσ(ζ). More generally, if
H is harmonic on D, continuous on D̄, and g ≤ H on ∂D, then g ≤ H throughout D."

**Formalization Note.**
* `D = D(c, R)` is the open disk `ball c R` in `ℂ`, `R > 0`; `D̄` is `closedBall c R`.
* `σ` is normalized arclength, so `∫_{∂D} F dσ` is Mathlib's `Real.circleAverage F c R`.
* `P_{D,a}(ζ) = (R² − |a − c|²)/|ζ − a|²` is Mathlib's `poissonKernel c a ζ` on the circle.
* `∆` is Mathlib's Laplacian on `ℂ` as a real inner product space (`∂²/∂x² + ∂²/∂y²`). "Harmonic
  on `D`" is `HarmonicOnNhd H D` (`C²` near each point of `D`, with vanishing Laplacian).
* Both sentences are conclusions, under the same hypotheses on `g`. -/
theorem fact_11 (g : ℂ → ℝ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hg_cont : ContinuousOn g (closedBall c R)) (hg_C2 : ContDiffOn ℝ 2 g (ball c R))
    (hg_sub : ∀ x ∈ ball c R, 0 ≤ Δ g x) :
    (∀ a ∈ ball c R, g a ≤ Real.circleAverage (fun ζ => g ζ * poissonKernel c a ζ) c R) ∧
    (∀ H : ℂ → ℝ, HarmonicOnNhd H (ball c R) → ContinuousOn H (closedBall c R) →
      (∀ ζ ∈ sphere c R, g ζ ≤ H ζ) → ∀ a ∈ ball c R, g a ≤ H a) := by sorry

end GaussMixHH
