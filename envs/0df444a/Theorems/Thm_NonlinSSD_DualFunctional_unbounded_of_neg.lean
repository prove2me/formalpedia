-- Prove2me | Theorems.Thm_NonlinSSD_DualFunctional_unbounded_of_neg
-- name    : NonlinSSD.DualFunctional.unbounded_of_neg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:10:42.972067+00:00
-- url     : https://prove2.me/theorems/085daf1b-0043-400c-92d1-e13f8f643c78
-- title:
--   Proof of Theorem 4, p. 13 — if P[ζ < 0] > 0 then D(v, ζ) = +∞
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $Y$ an integrable random variable, $a\le b$, $v\in\mathcal U_1([a,b])$ and $\zeta\in\mathcal L_\infty$. Let $D$ be the dual functional (34) of the dominance constraint with reference outcome $Y$. If the multiplier $\zeta$ is negative with positive probability,
--   $$P[\zeta<0]>0,$$
--   then
--   $$D(v,\zeta)=\sup_{X\in\mathcal L_1}\mathbb E\big[v(X)-v(Y)-\zeta X\big]=+\infty .$$
--
--   This is the first of the two cases in which the dual functional is infinite; together with the next milestone it shows that a finite value forces $\zeta\ge 0$ almost surely.
--
--   **Formalization Note** The paper states the unboundedness for $\sup_X \mathbb E[v(X)-\zeta X]$; the term $-\mathbb E\,v(Y)$ of (34) is a finite constant and does not change the value $+\infty$. $D$ is `EReal`-valued and $+\infty$ is $\top$. The standing data of the section are explicit: $Y$ integrable, $\zeta\in\mathcal L_\infty$ (`MemLp ζ ⊤ P`), $a\le b$.
-- source:
--   Dentcheva, Ruszczyński, Optimality and duality theory for stochastic optimization problems with nonlinear dominance constraints, author manuscript (rev. April 2003; Math. Program. 2004, DOI 10.1007/s10107-003-0453-z), p. 13, proof of Theorem 4

import Mathlib
import Definitions.Def_NonlinSSD_DualFunctional_Basic

open MeasureTheory

namespace NonlinSSD.DualFunctional

theorem unbounded_of_neg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Integrable Y P) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → ℝ) (hv : v ∈ NonlinSSD.Optimality.U1 a b) (ζ : Ω → ℝ) (hζ : MemLp ζ ⊤ P)
    (hneg : 0 < P {ω | ζ ω < 0}) :
    dualD P Y v ζ = ⊤ := by sorry

end NonlinSSD.DualFunctional
