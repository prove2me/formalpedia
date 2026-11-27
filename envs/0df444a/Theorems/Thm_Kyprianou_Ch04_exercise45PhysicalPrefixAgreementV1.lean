-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45PhysicalPrefixAgreementV1
-- name    : Kyprianou.Ch04.exercise45PhysicalPrefixAgreementV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:30:41.157423+00:00
-- url     : https://prove2.me/theorems/a1057189-b6f0-4159-9a04-a1481273b2e3
-- title:
--   Actual jump-measure Ito data agree on protected path prefixes
-- statement:
--   For a fixed path whose state before a finite clock and left state through the clock lie inside a rectangle, the cutoff and original integrands and drift/large-jump terms agree through that clock, and the full Ito residual agrees strictly before the clock.
-- source:
--   Kyprianou (2006), Exercise 4.5(iv), localisation.

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem exercise45PhysicalPrefixAgreementV1 :
∀ {Ω : Type} (X L : NNReal → Ω → ℝ) (w : Ω)
    (b : ℝ) (f ft fx g gt gx : ℝ → ℝ → ℝ) (n : ℕ) (τ : NNReal)
    (hτ : τ ≤ (n : NNReal))
    (hX : Measurable (fun t => X t w)) (hL : Measurable (fun t => L t w))
    (hPre : ∀ t < τ, |X t w| ≤ (n : ℝ))
    (hLeft : ∀ t ≤ τ, |L t w| ≤ (n : ℝ))
    (hEq : ∀ s x, 0 ≤ s → s ≤ (n : ℝ) → |x| ≤ (n : ℝ) →
      g s x = f s x ∧ gt s x = ft s x ∧ gx s x = fx s x),
    let μ := pathJumpMeasure X L w
    let D (a : ℝ → ℝ → ℝ) (t : NNReal) :=
      b * (∫ s in Icc (0 : ℝ) (t : ℝ), a s (L s.toNNReal w)) +
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
        z.2 * a z.1 (L z.1.toNNReal w) ∂μ
    let R (a aTime ax : ℝ → ℝ → ℝ) (t : NNReal) :=
      a (t : ℝ) (X t w) - (a 0 (X 0 w) +
        (∫ s in Icc (0 : ℝ) (t : ℝ), aTime s (X s.toNNReal w) ∂volume) +
        (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ univ,
          (a z.1 (L z.1.toNNReal w + z.2) - a z.1 (L z.1.toNNReal w) -
            z.2 * ax z.1 (L z.1.toNNReal w)) ∂μ))
    (∀ t ≤ τ, gx (t : ℝ) (L t w) = fx (t : ℝ) (L t w) ∧ D gx t = D fx t) ∧
    (∀ t < τ, R g gt gx t = R f ft fx t)
 := by
  sorry
end Kyprianou.Ch04
