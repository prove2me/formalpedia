-- Prove2me | Theorems.Thm_GameRandEnv_FirstOrder_eq_5_2
-- name    : GameRandEnv.FirstOrder.eq_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:51.464113+00:00
-- url     : https://prove2.me/theorems/80eec19b-137e-4ab6-bfa8-e027e8298ae8
-- title:
--   (5.2), p. 10 — for a minimizer π̄∗, Ξy = δF/δπ̄(π̄∗, ·, y) + η ln π∗(·|y) is π∗(·|y)-a.s. constant for m-a.s. y
-- statement:
--   In the setting of §2.1, let $F:\Pi\to\mathbb R$ satisfy Assumption 2.1, let $\eta>0$, and let $\bar\pi^*$ minimize $V=F+\eta H$ over $\Pi$. With $\pi^*(x|y)$ the density of $\bar\pi^*$ with respect to $\mathrm{Leb}\times\mathsf m$, put
--   $$\Xi_y(x)=\frac{\delta F}{\delta\bar\pi}(\bar\pi^*,x,y)+\eta\ln\pi^*(x|y).$$
--   Then for $\mathsf m$-a.e. $y$ the function $\Xi_y$ is $\pi^*(\cdot|y)$-a.s. equal to a constant: there is a measurable $\bar c:\mathbb Y\to\mathbb R$ with
--   $$\Xi_y(x)=\bar c(y)\qquad\text{for }\bar\pi^*\text{-a.e. }(x,y).$$
--
--   This is the "Gibbs form" of the minimizer on its support: up to a $y$-dependent normalization, $\pi^*(x|y)\propto\exp\!\big(-\tfrac1\eta\frac{\delta F}{\delta\bar\pi}(\bar\pi^*,x,y)\big)$ wherever $\pi^*$ is positive.
--
--   **Formalization Note** By the disintegration $\bar\pi^*(d\bar x)=\pi^*(dx|y)\mathsf m(dy)$ (Remark 2.2), "for $\mathsf m$-a.s. $y$, $\Xi_y$ is constant $\pi^*(\cdot|y)$-a.s." is stated as $\Xi=\bar c\circ\mathrm{pr}_{\mathbb Y}$ $\bar\pi^*$-a.e., which avoids conditional kernels. The constant is required to be measurable in $y$, as is the paper's $\bar c(y)=\int\Xi_y\,d\pi^*(\cdot|y)$.
-- source:
--   Conforti, Kazeykina, Ren, Game on random environment, mean-field Langevin system and neural networks, arXiv:2004.02457v2, p. 10, §5.1, proof of Theorem 3.1, Step 2, (5.2)

import Mathlib
import Definitions.Def_GameRandEnv_FirstOrder_Setting

open MeasureTheory Filter Topology

namespace GameRandEnv.FirstOrder

theorem eq_5_2 {d : ℕ} {Y : Type*} [MetricSpace Y] [CompleteSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (m : Measure Y) [IsProbabilityMeasure m] (p : ℝ)
    (F : Measure (Rd d × Y) → ℝ) (δF : Measure (Rd d × Y) → Rd d → Y → ℝ)
    (hA : Assumption21 m p F δF) (η : ℝ) (hη : 0 < η)
    (πs : Measure (Rd d × Y)) (hmin : IsMinimizer m p F η πs) :
    ∃ c : Y → ℝ, Measurable c ∧ ∀ᵐ z ∂πs, Xi m δF η πs z = c z.2 := by sorry

end GameRandEnv.FirstOrder
