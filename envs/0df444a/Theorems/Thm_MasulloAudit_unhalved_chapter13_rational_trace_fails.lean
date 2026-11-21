-- Prove2me | Theorems.Thm_MasulloAudit_unhalved_chapter13_rational_trace_fails
-- name    : MasulloAudit.unhalved_chapter13_rational_trace_fails
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:53:04.739713+00:00
-- url     : https://prove2.me/theorems/c3670090-7f5e-454b-bd48-595bbffba6b8
-- title:
--   The unhalved Chapter 13 trace identity fails over the rationals
-- statement:
--   Evaluate the real-place term of (13.3.1.4) by the unhalved finite-part value printed in (B.4.3.13). With that convention, the rational identity (13.3.1.3)–(13.3.1.5) fails. There is a smooth compactly supported real function $h$ with $h(0)>0$ and $\int h=0$ such that the corresponding rational radial tests $\phi_\varepsilon(t)=h(\log t/\varepsilon)$ violate this identity at all sufficiently small positive scales.
--
--   For any fixed real normalization constant $k$, the real part of the capped critical-line sum is strictly below the real part of the two polar terms minus the real-place finite part and $k h(0)$. The finite part uses the additive cutoff of (B.4.3.13). The real spectral sum is absolutely convergent, and every rational finite-place term vanishes under the standard kernel and Haar volume conditions. The support of $\phi_\varepsilon$ is at norms $t\in(1/2,2)$. The mean-zero condition is the degree-one condition (13.3.1.2) for these radial tests.
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, pp. 519, 522, Eqs. (12.5.1.1), (13.3.1.1)–(13.3.1.5), and Appendix B, (B.4.3.13), (B.4.4.1)–(B.4.4.2), (B.4.4.16). https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. The shrinking-test obstruction was pointed out by Calvin Yost-Wolff in the Prove2Me discussion of Theorem 13.3.1.1.

import Mathlib
import Definitions.Def_MasulloAudit_Chapter13Scalar

open MeasureTheory Filter
open MasulloAudit
open scoped SchwartzMap Topology

theorem MasulloAudit.unhalved_chapter13_rational_trace_fails :
    ∃ h : 𝓢(ℝ, ℝ), HasCompactSupport h ∧ 0 < h 0 ∧ (∫ x, h x) = 0 ∧
      ∀ k : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
        (∀ t : ℝ, t ≤ 1 / 2 ∨ 2 ≤ t → shrinkingRadialTest h ε t = 0) ∧
        Summable (rationalCappedSpectralTerm h ε) ∧
        (∀ (p : ℕ) [Fact p.Prime] [MeasurableSpace ℚ_[p] ] [BorelSpace ℚ_[p] ]
            (μ : Measure ℚ_[p]) [μ.IsAddHaarMeasure] (ψ : AddChar ℚ_[p] Circle),
          Continuous ψ → (∀ x : ℚ_[p], ψ x = 1 ↔ ‖x‖ ≤ 1) →
          μ (Metric.closedBall (0 : ℚ_[p]) 1) = 1 →
          let F : ℚ_[p] → ℂ := fun y ↦ (Real.log ‖y‖ : ℂ) *
            (∫ x, padicShiftedRadialTest (shrinkingRadialTest h ε) x * (ψ (x * y) : ℂ) ∂μ)
          Integrable F μ ∧ (∫ y, F y ∂μ) = 0) ∧
        ∃ v : ℝ, Tendsto (cutoffRealPlaceTranslated (fun x ↦ h (x / ε))) (𝓝[>] (0 : ℝ)) (𝓝 v) ∧
          (∑' ρ, rationalCappedSpectralTerm h ε ρ) <
            rationalPolarPair h ε - (v + k * h 0) := by sorry
