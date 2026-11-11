-- Prove2me | Theorems.Thm_OCEClocks_DisplayAds_lemma_18
-- name    : OCEClocks.DisplayAds.lemma_18
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:24:15.477307+00:00
-- url     : https://prove2.me/theorems/004a3613-b2cd-471c-9b89-5d1ad9ec5c04
-- title:
--   Lemma 18 — the first-win probability covers the dual increase ($\lambda=9/2$)
-- statement:
--   Let $\lambda=9/2$, let $\Gamma$ be the potential (6), and let $\nu$ be a reachable measure. For every request $x\in[0,1]$,
--
--   $$\nu\mathbf 1-\nu M_x\mathbf 1\ \ge\ \nu\Gamma-\nu M_x\Gamma+x\,\nu M_x\Gamma .$$
--
--   The left side is the probability of a first win on the request. The right side is the potential spent plus $x$ times the remaining potential. This is the accounting inequality that proves reverse weak duality at levels $w\le w_{ij}$ in Theorem 2; the paper's proof is computer-assisted (B.6).
--
--   **Formalization Note** $\nu\mathbf 1$ and $\nu M_x\mathbf 1$ are total masses, taken as real numbers (reachable measures are finite: $\nu\le\pi$). $\nu\Gamma$ and $\nu M_x\Gamma$ are integrals of $\Gamma$.
--
--   Differences from the source:
--   - encoding: expectations conditional on A(0) = a → the age process started at age a (last arrival at time −a, later arrivals at partial sums of i.i.d. Exp(λ) gaps, one independent Unif[0,1] for the request's clock); reason: this is how the paper evaluates these conditional expectations (proofs of Lemmas 16 and 32); by memorylessness it is the conditional law given A(0) = a
--   - reading: M⋆_x = lim_{ε↓0}(M_ε)^{x/ε}, formally exp(x L_M), in the potential Γ (6) and Γ⋆ = πΓ (7) → (M⋆_x 1)(a) is the probability that the infinitesimal-request age process started at age a has not stopped by time x; reason: the operator limit is informal in the paper; the paper identifies M⋆_x 1 with exactly this survival probability (p. 11 and the proof of Lemma 30)
--   - encoding: measures and functions on ages [0, ∞) → finite measures on ℝ and functions ℝ → ℝ; only ages a ≥ 0 occur, and boundedness/regularity hypotheses are imposed on [0, ∞) only; reason: Lean convention; same instances
-- source:
--   Huang, Patton, Yang, Zhao, Online Correlated Exponential Clocks, STOC 2027 submission (manuscript of November 3, 2026, sha256 820333a3…), p. 15, Lemma 18 (proof pp. 41–44, B.6)

import Mathlib
import Definitions.Def_OCEClocks_DisplayAds_Potential

open MeasureTheory

namespace OCEClocks.DisplayAds

/-- Lemma 18 (p. 15), with `λ = 9/2`: for every reachable measure `ν` and every request
`x ∈ [0, 1]`, `ν1 - νM_x1 ≥ νΓ - νM_xΓ + x νM_xΓ`. -/
theorem lemma_18 (ν : Measure ℝ) (hν : Reachable (9 / 2) ν) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ a, potential (9 / 2) a ∂ν) - (∫ a, potential (9 / 2) a ∂matchingKernelMeasure (9 / 2) x ν) +
        x * ∫ a, potential (9 / 2) a ∂matchingKernelMeasure (9 / 2) x ν ≤
      (ν Set.univ).toReal - (matchingKernelMeasure (9 / 2) x ν Set.univ).toReal := by sorry

end OCEClocks.DisplayAds
