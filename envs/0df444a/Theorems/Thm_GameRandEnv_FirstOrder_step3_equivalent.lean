-- Prove2me | Theorems.Thm_GameRandEnv_FirstOrder_step3_equivalent
-- name    : GameRandEnv.FirstOrder.step3_equivalent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:42.260149+00:00
-- url     : https://prove2.me/theorems/0ba852b7-e5f8-43a1-a4a8-1b077b2fff3d
-- title:
--   §5.1 Step 3, p. 11 — a minimizer π̄∗ of V over Π is equivalent to Leb × m
-- statement:
--   In the setting of §2.1, let $F:\Pi\to\mathbb R$ satisfy Assumption 2.1, let $\eta>0$, and let $\bar\pi^*$ minimize $V=F+\eta H$ over $\Pi$, where $H$ is relative entropy with respect to $\mathrm{Leb}\times\mathsf m$. Then $\bar\pi^*$ and $\mathrm{Leb}\times\mathsf m$ are mutually absolutely continuous:
--   $$\bar\pi^*\ll\mathrm{Leb}\times\mathsf m\qquad\text{and}\qquad\mathrm{Leb}\times\mathsf m\ll\bar\pi^* .$$
--
--   Equivalently, the density $\pi^*(x|y)$ is positive $\mathrm{Leb}\times\mathsf m$-a.e. Combined with (5.2) this shows that $\Xi_y$ is constant $\mathrm{Leb}$-a.e. for $\mathsf m$-a.e. $y$, from which the first-order equation (3.1) follows.
-- source:
--   Conforti, Kazeykina, Ren, Game on random environment, mean-field Langevin system and neural networks, arXiv:2004.02457v2, p. 11, §5.1, proof of Theorem 3.1, Step 3

import Mathlib
import Definitions.Def_GameRandEnv_FirstOrder_Setting

open MeasureTheory Filter Topology

namespace GameRandEnv.FirstOrder

theorem step3_equivalent {d : ℕ} {Y : Type*} [MetricSpace Y] [CompleteSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (m : Measure Y) [IsProbabilityMeasure m] (p : ℝ)
    (F : Measure (Rd d × Y) → ℝ) (δF : Measure (Rd d × Y) → Rd d → Y → ℝ)
    (hA : Assumption21 m p F δF) (η : ℝ) (hη : 0 < η)
    (πs : Measure (Rd d × Y)) (hmin : IsMinimizer m p F η πs) :
    πs ≪ volume.prod m ∧ volume.prod m ≪ πs := by sorry

end GameRandEnv.FirstOrder
