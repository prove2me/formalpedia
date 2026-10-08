-- Prove2me | Theorems.Thm_NonlinSSD_DualFunctional_dom_dualD
-- name    : NonlinSSD.DualFunctional.dom_dualD
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:22:33.945977+00:00
-- url     : https://prove2.me/theorems/df30f4b2-8db8-4acd-b6ae-876ce34303b0
-- title:
--   Proof of Theorem 4, p. 13 — dom D_i = {(v, ζ) : 0 ≤ ζ ≤ v′₋(a) a.s.}
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $Y$ an integrable random variable, $a\le b$, $v\in\mathcal U_1([a,b])$ and $\zeta\in\mathcal L_\infty$. Then the dual functional (34) is finite exactly on the set
--   $$\operatorname{dom}D=\{(v,\zeta):0\le\zeta\le v'_-(a)\ \text{a.s.}\},$$
--   that is,
--   $$D(v,\zeta)<+\infty\iff 0\le\zeta\le v'_-(a)\ \text{almost surely}.$$
--
--   This identifies the effective domain of the dual functional of one dominance constraint, the set over which the dual problem (31) is effectively posed in the multiplier $\zeta$.
--
--   **Formalization Note** $\operatorname{dom}D$ is the set where $D<+\infty$ (`< ⊤` in `EReal`). $D$ never equals $-\infty$, since $X=0$ gives a finite value.
-- source:
--   Dentcheva, Ruszczyński, Optimality and duality theory for stochastic optimization problems with nonlinear dominance constraints, author manuscript (rev. April 2003; Math. Program. 2004, DOI 10.1007/s10107-003-0453-z), p. 13, proof of Theorem 4

import Mathlib
import Definitions.Def_NonlinSSD_DualFunctional_Basic

open MeasureTheory

namespace NonlinSSD.DualFunctional

theorem dom_dualD {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Integrable Y P) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → ℝ) (hv : v ∈ NonlinSSD.Optimality.U1 a b) (ζ : Ω → ℝ) (hζ : MemLp ζ ⊤ P) :
    dualD P Y v ζ < ⊤ ↔ ∀ᵐ ω ∂P, 0 ≤ ζ ω ∧ ζ ω ≤ leftDeriv v a := by sorry

end NonlinSSD.DualFunctional
