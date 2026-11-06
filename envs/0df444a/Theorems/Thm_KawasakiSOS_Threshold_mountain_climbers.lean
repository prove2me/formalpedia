-- Prove2me | Theorems.Thm_KawasakiSOS_Threshold_mountain_climbers
-- name    : KawasakiSOS.Threshold.mountain_climbers
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:01:13.045713+00:00
-- url     : https://prove2.me/theorems/62cbee2e-2260-4984-a4e4-2d2680c69378
-- title:
--   Theorem 4.3: mountain climbers
-- statement:
--   Let $f,g:[0,1]\to[0,1]$ be continuous and piecewise monotone, with $f(0)=g(0)=0$ and $f(1)=g(1)=1$. Then there are continuous surjections $\varphi,\psi:[0,1]\to[0,1]$ with $\varphi(0)=\psi(0)=0$, $\varphi(1)=\psi(1)=1$ and
--
--   $$f\circ\varphi=g\circ\psi.$$
--
--   Two climbers can thus ascend the two sides of a mountain from sea level to the summit while always staying at the same height. In this mission the theorem steers the two windows of the canonical path.
--
--   Differences from the source:
--   - reading: "piecewise monotone" → a finite partition with f weakly monotone or weakly antitone on each piece; reason: the application has flat pieces where d(i) = 0, so monotone is read weakly
--   - encoding: f, g, ϕ, ψ : [0,1] → [0,1] → functions ℝ → ℝ with ContinuousOn and MapsTo on Set.Icc 0 1; reason: values outside [0,1] are irrelevant
-- source:
--   Giriyan, Randall, Richa, A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model, STOC 2027 submission manuscript (sha256 fa335117…), Theorem 4.3, p. 10 (PDF p. 11)

import Mathlib
import Definitions.Def_KawasakiSOS_Threshold_IsPiecewiseMonotone

namespace KawasakiSOS.Threshold

/-- Giriyan, Randall, Richa, *A Sharp Threshold for Kawasaki Mixing in a Fixed-Magnetization SOS Model*, STOC 2027 submission manuscript (sha256 fa335117…), Theorem 4.3, p. 10 (PDF p. 11).

Formalization Notes:
- reading: "piecewise monotone" → a finite partition with f weakly monotone or weakly antitone on each piece. The application has flat pieces where d(i) = 0, so monotone is read weakly.
- encoding: f, g, ϕ, ψ : [0,1] → [0,1] → functions ℝ → ℝ with ContinuousOn and MapsTo on Set.Icc 0 1. Values outside [0,1] are irrelevant. -/
theorem mountain_climbers (f g : ℝ → ℝ) (hfc : ContinuousOn f (Set.Icc 0 1)) (hgc : ContinuousOn g (Set.Icc 0 1)) (hfm : Set.MapsTo f (Set.Icc 0 1) (Set.Icc 0 1)) (hgm : Set.MapsTo g (Set.Icc 0 1) (Set.Icc 0 1)) (hfp : IsPiecewiseMonotone f) (hgp : IsPiecewiseMonotone g) (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hf1 : f 1 = 1) (hg1 : g 1 = 1) :
    ∃ φ ψ : ℝ → ℝ, ContinuousOn φ (Set.Icc 0 1) ∧ ContinuousOn ψ (Set.Icc 0 1) ∧
      Set.MapsTo φ (Set.Icc 0 1) (Set.Icc 0 1) ∧ Set.MapsTo ψ (Set.Icc 0 1) (Set.Icc 0 1) ∧
      Set.SurjOn φ (Set.Icc 0 1) (Set.Icc 0 1) ∧ Set.SurjOn ψ (Set.Icc 0 1) (Set.Icc 0 1) ∧
      φ 0 = 0 ∧ ψ 0 = 0 ∧ φ 1 = 1 ∧ ψ 1 = 1 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, f (φ t) = g (ψ t) := by sorry

end KawasakiSOS.Threshold
