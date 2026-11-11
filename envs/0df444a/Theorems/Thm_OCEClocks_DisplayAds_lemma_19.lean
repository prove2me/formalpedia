-- Prove2me | Theorems.Thm_OCEClocks_DisplayAds_lemma_19
-- name    : OCEClocks.DisplayAds.lemma_19
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:23:52.744676+00:00
-- url     : https://prove2.me/theorems/399982ed-4d8a-4bc9-a0b6-84f57f5cc325
-- title:
--   Lemma 19 — a gap consumes potential at rate at most the potential already spent ($\lambda=9/2$)
-- statement:
--   Let $\lambda=9/2$, let $\Gamma$ be the potential (6) and $\Gamma^\star=\pi\Gamma$, and let $\nu$ be a reachable measure. For every $x\ge0$,
--
--   $$0\ \le\ -\frac{d}{dx}\,\nu G_x\Gamma\ \le\ \Gamma^\star-\nu G_x\Gamma,$$
--
--   with a right derivative at $x=0$.
--
--   A gap can lower the remaining potential without covering a level. The lemma bounds this loss by the dual already recorded, which is what reverse weak duality needs at levels $w>w_{ij}$ in Theorem 2.
--
--   **Formalization Note** The statement asserts that $t\mapsto\nu G_t\Gamma$ has a derivative $d$ at $x$ within $[0,\infty)$ (the ordinary derivative for $x>0$, the right derivative at $x=0$), and that $0\le -d\le\Gamma^\star-\nu G_x\Gamma$.
--
--   Differences from the source:
--   - encoding: expectations conditional on A(0) = a → the age process started at age a (last arrival at time −a, later arrivals at partial sums of i.i.d. Exp(λ) gaps, one independent Unif[0,1] for the request's clock); reason: this is how the paper evaluates these conditional expectations (proofs of Lemmas 16 and 32); by memorylessness it is the conditional law given A(0) = a
--   - reading: M⋆_x = lim_{ε↓0}(M_ε)^{x/ε}, formally exp(x L_M), in the potential Γ (6) and Γ⋆ = πΓ (7) → (M⋆_x 1)(a) is the probability that the infinitesimal-request age process started at age a has not stopped by time x; reason: the operator limit is informal in the paper; the paper identifies M⋆_x 1 with exactly this survival probability (p. 11 and the proof of Lemma 30)
--   - encoding: measures and functions on ages [0, ∞) → finite measures on ℝ and functions ℝ → ℝ; only ages a ≥ 0 occur, and boundedness/regularity hypotheses are imposed on [0, ∞) only; reason: Lean convention; same instances
--   - encoding: −(d/dx) νG_xΓ for x ≥ 0, right derivative at x = 0 → ∃ d, HasDerivWithinAt (t ↦ νG_tΓ) d (Ici 0) x, then the bounds on −d; reason: the derivative within [0, ∞) is the ordinary derivative at x > 0 and the right derivative at 0; existence is part of the claim
-- source:
--   Huang, Patton, Yang, Zhao, Online Correlated Exponential Clocks, STOC 2027 submission (manuscript of November 3, 2026, sha256 820333a3…), p. 16, Lemma 19 (proof p. 43, B.7)

import Mathlib
import Definitions.Def_OCEClocks_DisplayAds_Potential

open MeasureTheory

namespace OCEClocks.DisplayAds

/-- Lemma 19 (p. 16), with `λ = 9/2`: for every reachable measure `ν` and every `x ≥ 0`, the map
`x ↦ νG_xΓ` has a derivative at `x` (a right derivative at `x = 0`) whose negative lies between
`0` and `Γ⋆ - νG_xΓ`. -/
theorem lemma_19 (ν : Measure ℝ) (hν : Reachable (9 / 2) ν) (x : ℝ) (hx : 0 ≤ x) :
    ∃ d : ℝ,
      HasDerivWithinAt (fun t => ∫ a, potential (9 / 2) a ∂gapKernelMeasure (9 / 2) t ν) d
        (Set.Ici 0) x ∧
      0 ≤ -d ∧
      -d ≤ targetRatio (9 / 2) - ∫ a, potential (9 / 2) a ∂gapKernelMeasure (9 / 2) x ν := by sorry

end OCEClocks.DisplayAds
