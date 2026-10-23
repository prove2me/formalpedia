-- Prove2me | Theorems.Thm_GameRandEnv_FirstOrder_sufficient_convexity_bound
-- name    : GameRandEnv.FirstOrder.sufficient_convexity_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:42.127812+00:00
-- url     : https://prove2.me/theorems/b38e9871-aa4f-4eb3-b80b-98bea66a04e5
-- title:
--   §5.1 sufficient condition, p. 11 — for convex F, F(π̄) − F(π̄∗) ≥ ∫ δF/δπ̄(π̄∗, ·) d(π̄ − π̄∗)
-- statement:
--   In the setting of §2.1, let $F:\Pi\to\mathbb R$ satisfy Assumption 2.1 and be convex on $\Pi$, i.e. $F((1-t)\nu+t\nu')\le(1-t)F(\nu)+tF(\nu')$ for $\nu,\nu'\in\Pi$ and $t\in[0,1]$. Then for all $\bar\pi^*,\bar\pi\in\Pi$,
--   $$F(\bar\pi)-F(\bar\pi^*)\ge\int\frac{\delta F}{\delta\bar\pi}(\bar\pi^*,\bar x)\,(\bar\pi-\bar\pi^*)(d\bar x).$$
--
--   This is the tangent-line inequality for convex functionals of measures, expressed through the linear functional derivative; it is the $F$-half of the sufficiency direction of Theorem 3.1.
--
--   **Formalization Note** The page states it for $\bar\pi^*$ satisfying (3.1) and $\bar\pi\ll\mathrm{Leb}\times\mathsf m$; the argument uses neither, so they are not hypotheses here. $\int g\,d(\bar\pi-\bar\pi^*)$ is written as $\int g\,d\bar\pi-\int g\,d\bar\pi^*$.
-- source:
--   Conforti, Kazeykina, Ren, Game on random environment, mean-field Langevin system and neural networks, arXiv:2004.02457v2, p. 11, §5.1, proof of Theorem 3.1, Sufficient condition

import Mathlib
import Definitions.Def_GameRandEnv_FirstOrder_Setting

open MeasureTheory Filter Topology

namespace GameRandEnv.FirstOrder

theorem sufficient_convexity_bound {d : ℕ} {Y : Type*} [MetricSpace Y] [CompleteSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (m : Measure Y) [IsProbabilityMeasure m] (p : ℝ)
    (F : Measure (Rd d × Y) → ℝ) (δF : Measure (Rd d × Y) → Rd d → Y → ℝ)
    (hA : Assumption21 m p F δF)
    (hconv : ConvexOnPi m p F) (πs π : Measure (Rd d × Y)) (hπs : πs ∈ Pi m p)
    (hπ : π ∈ Pi m p) :
    pairDiff (fun z => δF πs z.1 z.2) πs π ≤ F π - F πs := by sorry

end GameRandEnv.FirstOrder
