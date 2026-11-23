-- Prove2me | Theorems.Thm_MMDarkPool_Exchange_Supplement_controlled_measure_refutation
-- name    : MMDarkPool.Exchange.Supplement.controlled_measure_refutation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T18:24:35.656323+00:00
-- url     : https://prove2.me/theorems/75c4efd4-f5c2-42fa-a3ea-30cda0d7a9aa
-- title:
--   §2.2.1, p. 5 (corrected: refutation) — the printed density and controlled intensities are incompatible
-- statement:
--   For every ε,r > 0, the constructed parameters satisfy Standing, and the constant unit posting belongs to the source volume sets and satisfies each per-side sum constraint. Every baseline rate equals exp(−1/2), whereas every size-2 fill intensity is zero. The printed density is strictly positive on every path, for any integrated gates, and no reference measure, count and controlled measure can satisfy TerminalMeasureRequirements.
--
--   $$\lambda^{i,j}=e^{-1/2},\qquad\lambda^{\mathcal L,i,j,2}=0,\qquad R>0,\qquad\mathbb E^0[N_1]=\epsilon>0,\quad\mathbb E^{\mathcal L}[N_1]=0.$$
--
--   These requirements are incompatible: zero mean of a nonnegative count forces it to vanish almost surely, and the strictly positive measurable density preserves null sets. This refutes the paper’s simultaneous controlled-intensity and density specification. It is a companion result, independent of the proof of the published goal.
--
--   **Formalization Note.** Reference Poisson counts at unit time have mean ε. A zero-compensator martingale starting at zero has terminal mean zero. The theorem refutes even these necessary consequences, with explicit count integrability and density measurability. Gate integrals are abstracted after pulling out the constant baseline coefficients. A, θ, σ and tick remain fixed at 1 while ε and impact r may be arbitrarily small. No claim about a chosen latency law, Brownian construction or the published base statements is made.
--
--   Differences from the source:
--   - correction: The controlled measure has both the printed density and the prescribed size-specific intensities (pp. 5–6). → A constant admissible numerical instance makes their necessary terminal consequences incompatible.; reason: The printed exponential density is strictly positive, so a measurable such density preserves null sets. An unposted size-2 count is prescribed compensator zero but has positive reference mean ε at T = 1. The source claim is refuted rather than silently repairing the density.
--   - generalization: The reference count is Poisson with rate ε and the controlled count minus its compensator is a martingale, starting at zero. → Only their integrable terminal-mean consequences are required, and the integrated inventory/size gates may be arbitrary real functions giving a measurable density.; reason: Impossibility with fewer stochastic assumptions applies to every model the source allows. Strict positivity of an exponential makes the particular gate integrals irrelevant. The parameters A, θ, σ and tick are fixed at 1 while ε and the positive impact r may be arbitrarily small.
--   - encoding: The printed density is an exponential of stochastic integrals with constant baseline coefficients in this instance. → activeCounts and activeTimes denote the already integrated indicators, and withDensity encodes the terminal change of measure.; reason: Pulling constant coefficients outside the two integrals yields exactly printedDensity. The density and count are explicitly measurable, and both count integrals require Integrable, so no totality default is used.
-- source:
--   Baldacci, Manziuk, Mastrolia & Rosenbaum, arXiv:1912.01129v1, §2.2.1, pp. 4–6, controlled intensities and printed change-of-measure density.

import Mathlib
import Definitions.Def_MMDarkPool_Exchange_Supplement_MeasureCounterexample

namespace MMDarkPool.Exchange.Supplement

/-- The printed density and controlled intensity cannot both describe the
constant admissible posting of this source instance. No latency law is used. -/
theorem controlled_measure_refutation (ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) :
    Standing (counterParams ε r) ∧
    (∀ i j, ∃ k ∈ (counterParams ε r).V j, counterPosting i j = (k : ℝ)) ∧
    (∀ i, counterPosting i Pool.l + counterPosting i Pool.d ∈
      Set.Icc 0 (2 * (counterParams ε r).qbar)) ∧
    (∀ i j, lam (counterParams ε r) i j counterPosting = Real.exp (-(1 / 2 : ℝ))) ∧
    (∀ q i j, lamK (counterParams ε r) q i j 2 counterPosting = 0) ∧
    (∀ {Ω : Type*} [MeasurableSpace Ω]
      (activeCounts activeTimes : Side → Pool → ℕ → Ω → ℝ) (ω : Ω),
      0 < printedDensity ε r activeCounts activeTimes ω) ∧
    (∀ {Ω : Type*} [MeasurableSpace Ω] (μ₀ : MeasureTheory.Measure Ω) (N : Ω → ℕ)
      (activeCounts activeTimes : Side → Pool → ℕ → Ω → ℝ),
      ¬ TerminalMeasureRequirements ε r μ₀ N activeCounts activeTimes) := by sorry

end MMDarkPool.Exchange.Supplement
