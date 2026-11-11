-- Prove2me | Theorems.Thm_OCEClocks_DisplayAds_lemma_17
-- name    : OCEClocks.DisplayAds.lemma_17
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:24:12.42898+00:00
-- url     : https://prove2.me/theorems/fad8f78e-f73a-40b6-8056-65fa71c208cc
-- title:
--   Lemma 17 — the potentials $\nu M_x\Gamma$ and $\nu G_x\Gamma$ are continuous and nonincreasing in $x\in[0,1]$ ($\lambda=9/2$)
-- statement:
--   Let $\lambda=9/2$, let $\Gamma$ be the potential (6), and let $\nu$ be a reachable measure. Then both
--
--   $$x\mapsto\nu M_x\Gamma=\int\Gamma\,d(\nu M_x)\qquad\text{and}\qquad x\mapsto\nu G_x\Gamma=\int\Gamma\,d(\nu G_x)$$
--
--   are continuous and nonincreasing on $[0,1]$.
--
--   This makes every advertiser's offer (13) continuous and nonincreasing in the allocated mass, so the water-filling step of the Display Ads algorithm is well defined.
--
--   **Formalization Note** Both functions are real integrals of $\Gamma$ against the kernel images of $\nu$, as `ContinuousOn` and `AntitoneOn` on `Set.Icc 0 1`.
--
--   Differences from the source:
--   - encoding: expectations conditional on A(0) = a → the age process started at age a (last arrival at time −a, later arrivals at partial sums of i.i.d. Exp(λ) gaps, one independent Unif[0,1] for the request's clock); reason: this is how the paper evaluates these conditional expectations (proofs of Lemmas 16 and 32); by memorylessness it is the conditional law given A(0) = a
--   - reading: M⋆_x = lim_{ε↓0}(M_ε)^{x/ε}, formally exp(x L_M), in the potential Γ (6) and Γ⋆ = πΓ (7) → (M⋆_x 1)(a) is the probability that the infinitesimal-request age process started at age a has not stopped by time x; reason: the operator limit is informal in the paper; the paper identifies M⋆_x 1 with exactly this survival probability (p. 11 and the proof of Lemma 30)
--   - encoding: measures and functions on ages [0, ∞) → finite measures on ℝ and functions ℝ → ℝ; only ages a ≥ 0 occur, and boundedness/regularity hypotheses are imposed on [0, ∞) only; reason: Lean convention; same instances
-- source:
--   Huang, Patton, Yang, Zhao, Online Correlated Exponential Clocks, STOC 2027 submission (manuscript of November 3, 2026, sha256 820333a3…), p. 15, Lemma 17 (proof pp. 40–43, B.5)

import Mathlib
import Definitions.Def_OCEClocks_DisplayAds_Potential

open MeasureTheory

namespace OCEClocks.DisplayAds

/-- Lemma 17 (p. 15), with `λ = 9/2`: for every reachable measure `ν`, the potentials `νM_xΓ` and
`νG_xΓ` are continuous and nonincreasing in `x` on `[0, 1]`. -/
theorem lemma_17 (ν : Measure ℝ) (hν : Reachable (9 / 2) ν) :
    ContinuousOn (fun x => ∫ a, potential (9 / 2) a ∂matchingKernelMeasure (9 / 2) x ν)
      (Set.Icc 0 1) ∧
    AntitoneOn (fun x => ∫ a, potential (9 / 2) a ∂matchingKernelMeasure (9 / 2) x ν)
      (Set.Icc 0 1) ∧
    ContinuousOn (fun x => ∫ a, potential (9 / 2) a ∂gapKernelMeasure (9 / 2) x ν)
      (Set.Icc 0 1) ∧
    AntitoneOn (fun x => ∫ a, potential (9 / 2) a ∂gapKernelMeasure (9 / 2) x ν)
      (Set.Icc 0 1) := by sorry

end OCEClocks.DisplayAds
