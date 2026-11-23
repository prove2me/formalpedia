-- Prove2me | Theorems.Thm_OptimalTraceDistance_Estimation_rounded_algorithm_realization
-- name    : OptimalTraceDistance.Estimation.rounded_algorithm_realization
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-23T10:11:04.474146+00:00
-- url     : https://prove2.me/theorems/245927bd-6e92-4831-8837-95829fc03dff
-- title:
--   Rounded Algorithm 2 is realized by one POVM
-- statement:
--   **Realization of the rounded two-stage algorithm as one measurement.**
--
--   Fix constants $C>0$, $d_0\ge2$, a dimension $d\ge2$ and an accuracy $0<\varepsilon\le1/32$, and let $N$ be the copy count of Algorithm 2 ($\lceil C_0d^2/\varepsilon^2\rceil$ if $d<d_0$, and $\lceil C_0d\log^2d\rceil+\lceil C\,\mathrm{rate}(d,\varepsilon)\rceil$ otherwise). There is a single two-state measurement $M$ on $N$ copies of $\rho$ and $N$ copies of $\sigma$, chosen before the states are known, such that for all density matrices $\rho,\sigma$ and every Borel set $B\subseteq\mathbb R$,
--
--   $$
--   \Pr_{M}(\text{outcome}\in B)=W^{\mathrm{rnd}}_{C,d_0,\varepsilon}(\rho,\sigma;B),
--   $$
--
--   where $W^{\mathrm{rnd}}$ is the event weight of the rounded variant of Algorithm 2 (definition `OptimalTraceDistance_Estimation_RoundedAlgorithm`), in which each Keyl report is computed from the Keyl unitary rounded to a finite grid of unitaries.
--
--   In the large-dimension branch the measurement first prepares copies of $(\rho+\sigma)/2$ by a uniformly random choice between the $\rho$- and $\sigma$-copy in each position, applies Keyl's measurement, and, given the rounded report, measures the spectral decomposition of the polynomial observable on freshly labelled copies; it outputs the clipped eigenvalue. In the small-dimension branch it applies Keyl's measurement to the copies of $\rho$ and of $\sigma$ separately and outputs the trace distance of the two rounded reports. Because the rounded reports take finitely many values, the adaptive second stage is a finite sum of tensor products.
--
--   This is the finite-outcome analogue of the platform theorem `algorithm_2_realization_uniform` and serves the same purpose in the proof of Theorem 1.1.
-- source:
--   Chen–Gao–Wang, Optimal Trace Distance Estimation, STOC 2027 submission #875, Algorithm 2 (p.11) and §5 (p.21); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/875.pdf. Rounded (finite-report) variant of the platform theorem algorithm_2_realization_uniform; Keyl measurement from O'Donnell–Wright arXiv:1508.01907 pp.6–8.

import Definitions.Def_OptimalTraceDistance_Estimation_RoundedAlgorithm

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
noncomputable section

namespace OptimalTraceDistance.Estimation

theorem rounded_algorithm_realization : ∀ C : ℝ, 0 < C → ∀ d₀ : ℕ, 2 ≤ d₀ →
    ∀ d : ℕ, 2 ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1/32 →
      ∃ M : TwoStateMeasurement d (algorithmCost C d₀ d ε),
        ∀ (ρ σ : Mat d) (hρ : Density ρ) (hσ : Density σ),
          ∀ B : Set ℝ, MeasurableSet B → outcomeLaw M ρ σ hρ hσ B =
            roundedAlgorithmWeight C d₀ ε ρ σ hρ hσ B := by sorry

end OptimalTraceDistance.Estimation
