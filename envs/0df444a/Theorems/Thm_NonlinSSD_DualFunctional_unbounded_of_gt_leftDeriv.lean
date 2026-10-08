-- Prove2me | Theorems.Thm_NonlinSSD_DualFunctional_unbounded_of_gt_leftDeriv
-- name    : NonlinSSD.DualFunctional.unbounded_of_gt_leftDeriv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:13:42.51528+00:00
-- url     : https://prove2.me/theorems/61aeb5bb-121e-42a3-8e9f-14c1bcd7f62a
-- title:
--   Proof of Theorem 4, p. 13 — if P[ζ > v′₋(a)] > 0 then D(v, ζ) = +∞
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $Y$ an integrable random variable, $a\le b$, $v\in\mathcal U_1([a,b])$ and $\zeta\in\mathcal L_\infty$. Let $D$ be the dual functional (34) and $v'_-(a)$ the left derivative of $v$ at $a$ (the slope of $v$ on $(-\infty,a]$). If
--   $$P\big[\zeta>v'_-(a)\big]>0,$$
--   then
--   $$D(v,\zeta)=+\infty .$$
--
--   This is the second unbounded case of the proof of Theorem 4: a multiplier exceeding the left slope of the utility at $a$ with positive probability makes the dual functional infinite.
--
--   **Formalization Note** As in the previous milestone, the finite term $-\mathbb E\,v(Y)$ does not affect the value $+\infty$ ($\top$ in `EReal`). The left derivative is `derivWithin v (Set.Iic a) a`.
-- source:
--   Dentcheva, Ruszczyński, Optimality and duality theory for stochastic optimization problems with nonlinear dominance constraints, author manuscript (rev. April 2003; Math. Program. 2004, DOI 10.1007/s10107-003-0453-z), p. 13, proof of Theorem 4

import Mathlib
import Definitions.Def_NonlinSSD_DualFunctional_Basic

open MeasureTheory

namespace NonlinSSD.DualFunctional

theorem unbounded_of_gt_leftDeriv {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Integrable Y P) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → ℝ) (hv : v ∈ NonlinSSD.Optimality.U1 a b) (ζ : Ω → ℝ) (hζ : MemLp ζ ⊤ P)
    (hgt : 0 < P {ω | leftDeriv v a < ζ ω}) :
    dualD P Y v ζ = ⊤ := by sorry

end NonlinSSD.DualFunctional
