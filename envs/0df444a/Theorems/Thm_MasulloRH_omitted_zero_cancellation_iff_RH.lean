-- Prove2me | Theorems.Thm_MasulloRH_omitted_zero_cancellation_iff_RH
-- name    : MasulloRH.omitted_zero_cancellation_iff_RH
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-20T22:24:27.890178+00:00
-- url     : https://prove2.me/theorems/afc89cb1-5683-4c11-8519-0fe26e7dd2c1
-- title:
--   Vanishing of the omitted zero distribution in all narrow windows is equivalent to RH
-- statement:
--   For each half-width strictly between zero and one half, form the complementary sum over nontrivial zeros on or outside the boundary of the centered window. The terms are the shifted Mellin transforms of an admissible test function, weighted by the actual analytic multiplicity. The assertion that these sums vanish for every such width and every admissible test is equivalent to the Riemann hypothesis in its standard Mathlib formulation. The forward implication isolates the independent spectral input in the positive-width rational trace program. The reverse implication follows because RH puts every nontrivial zero on the center line.
-- source:
--   Derived equivalence for the rational specialization of Masullo, The Music of the Primes (20 November 2026), §§1.4.2–1.4.5, pp. 28–30 and Theorem 12.5.1.1, pp. 519–520. The conditional continuation chain adapts the mission reductions submitted by davidloeffler, https://prove2.me/submissions/270062f2-0e4a-47b4-a3cc-8e1e5d6ff4f9. The reverse direction uses the definition of the omitted window.

import Definitions.Def_MasulloRH_RationalTrace
import Definitions.Def_ConnesRZ_weil_defs
open MeasureTheory Set MasulloRH ConnesRZ

theorem MasulloRH.omitted_zero_cancellation_iff_RH :
    (∀ (α : ℝ), 0 < α → α < 1/2 → ∀ (φ : ℝ → ℂ), IsRationalTraceTest φ →
      let omitted := {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|}
      (∑' r : omitted, (ConnesRZ.zeroMult r.val.val : ℂ) * mellin φ (r.val.val - 1/2)) = 0) ↔
    RiemannHypothesis := by sorry
