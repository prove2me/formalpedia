-- Prove2me | Theorems.Thm_HunterPDE_HeatFourier_heat_L2_Linfty_estimate
-- name    : HunterPDE.HeatFourier.heat_L2_Linfty_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:59:57.686871+00:00
-- url     : https://prove2.me/theorems/326da9bf-4af9-4684-aaf8-1b1c6677ed75
-- title:
--   Theorem 5.8 — ‖u(t)‖_{L²} ≤ ‖f‖_{L²} and ‖u(t)‖_{L^∞} ≤ (4πt)^{−n/2} ‖f‖_{L¹}
-- statement:
--   Let $f \in \mathcal S(\mathbb{R}^n)$ be real-valued, let $u$ be the Schwartz solution of the heat problem constructed in Theorem 5.4, and let $t > 0$. Then
--   $$\|u(t)\|_{L^2} \le \|f\|_{L^2}, \qquad \|u(t)\|_{L^\infty} \le \frac{1}{(4\pi t)^{n/2}}\, \|f\|_{L^1}.$$
--   These are the two basic spatial estimates of the heat flow; interpolating between them gives the $L^{p'} \to L^p$ bound (5.10).
--
--   **Formalization Note.** $u$ is any curve satisfying `IsSchwartzHeatSolution (Set.Ici 0) f u` (the solution is unique by Theorem 5.4). Norms are Mathlib's `eLpNorm` for Lebesgue measure, valued in $[0,\infty]$; the constant $(4\pi t)^{-n/2}$ is exact.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 134, Theorem 5.8

import Mathlib
import Definitions.Def_HunterPDE_HeatFourier_SchwartzCurve

namespace HunterPDE.HeatFourier

open MeasureTheory
open scoped SchwartzMap ENNReal

/-- Hunter, *Notes on PDEs*, p. 134, Theorem 5.8: let `u : [0, ∞) → 𝓢(ℝⁿ)` be the solution of
(5.2) constructed in Theorem 5.4 (any solution in `C([0, ∞); 𝓢) ∩ C¹(0, ∞; 𝓢)`; it is unique)
and `t > 0`. Then
`‖u(t)‖_{L²} ≤ ‖f‖_{L²}` and `‖u(t)‖_{L^∞} ≤ 1/(4πt)^{n/2} · ‖f‖_{L¹}`.
Norms are Mathlib's `eLpNorm` for Lebesgue measure, valued in `[0, ∞]`. -/
theorem heat_L2_Linfty_estimate (n : ℕ) (f : 𝓢(EuclideanSpace ℝ (Fin n), ℝ))
    (u : ℝ → 𝓢(EuclideanSpace ℝ (Fin n), ℝ)) (hu : IsSchwartzHeatSolution (Set.Ici 0) f u)
    (t : ℝ) (ht : 0 < t) :
    eLpNorm (u t) 2 volume ≤ eLpNorm f 2 volume ∧
    eLpNorm (u t) ∞ volume ≤
      ENNReal.ofReal (1 / (4 * Real.pi * t) ^ ((n : ℝ) / 2)) * eLpNorm f 1 volume := by sorry

end HunterPDE.HeatFourier
