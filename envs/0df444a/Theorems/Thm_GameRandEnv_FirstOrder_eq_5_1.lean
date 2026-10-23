-- Prove2me | Theorems.Thm_GameRandEnv_FirstOrder_eq_5_1
-- name    : GameRandEnv.FirstOrder.eq_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:42.448818+00:00
-- url     : https://prove2.me/theorems/f446ad5d-d993-4b44-b1fe-2b7233c7c503
-- title:
--   (5.1), p. 10 — for a minimizer π̄∗ and any π̄ ∈ Π with H(π̄) < ∞, 0 ≤ ∫ (δF/δπ̄(π̄∗, ·) + η ln π∗) d(π̄ − π̄∗)
-- statement:
--   In the setting of §2.1, let $F:\Pi\to\mathbb R$ satisfy Assumption 2.1, let $\eta>0$, and let $\bar\pi^*$ minimize $V=F+\eta H$ over $\Pi$, where $H$ is relative entropy with respect to $\mathrm{Leb}\times\mathsf m$. Let $\pi^*(x|y)$ be the density of $\bar\pi^*$ with respect to $\mathrm{Leb}\times\mathsf m$ and
--   $$\Xi(\bar x)=\frac{\delta F}{\delta\bar\pi}(\bar\pi^*,\bar x)+\eta\ln\pi^*(x|y).$$
--   Then for every $\bar\pi\in\Pi$ with $H(\bar\pi)<\infty$:
--   1. $\bar\pi\{\pi^*(x|y)=0\}=0$;
--   2. $\Xi$ is integrable with respect to both $\bar\pi$ and $\bar\pi^*$;
--   3. the variational inequality (5.1) holds:
--   $$0\le\int\Big(\frac{\delta F}{\delta\bar\pi}(\bar\pi^*,\bar x)+\eta\ln\pi^*(x|y)\Big)(\bar\pi-\bar\pi^*)(d\bar x).$$
--
--   This is the first-order variational inequality of the minimization: no admissible direction $\bar\pi-\bar\pi^*$ decreases $V$ to first order. Steps 2 and 3 of the proof of Theorem 3.1 apply it to specially constructed $\bar\pi$.
--
--   **Formalization Note** On the page $\ln 0=-\infty$, so the right-hand side of (5.1) is $-\infty$ if $\bar\pi$ charges $\{\pi^*=0\}$, or if the integral is not finite; (5.1) therefore asserts items 1 and 2, which are made explicit because Lean's `Real.log 0 = 0` and the Bochner integral of a non-integrable function is $0$. The middle term $\limsup_{\varepsilon\to0}(V(\bar\pi^\varepsilon)-V(\bar\pi^*))/\varepsilon$ of (5.1) is a step of the proof and is omitted.
-- source:
--   Conforti, Kazeykina, Ren, Game on random environment, mean-field Langevin system and neural networks, arXiv:2004.02457v2, p. 10, §5.1, proof of Theorem 3.1, (5.1)

import Mathlib
import Definitions.Def_GameRandEnv_FirstOrder_Setting

open MeasureTheory Filter Topology

namespace GameRandEnv.FirstOrder

theorem eq_5_1 {d : ℕ} {Y : Type*} [MetricSpace Y] [CompleteSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (m : Measure Y) [IsProbabilityMeasure m] (p : ℝ)
    (F : Measure (Rd d × Y) → ℝ) (δF : Measure (Rd d × Y) → Rd d → Y → ℝ)
    (hA : Assumption21 m p F δF) (η : ℝ) (hη : 0 < η)
    (πs π : Measure (Rd d × Y)) (hmin : IsMinimizer m p F η πs) (hπ : π ∈ Pi m p)
    (hH : relEnt m π < ⊤) :
    π {z | πs.rnDeriv (volume.prod m) z = 0} = 0 ∧
      Integrable (Xi m δF η πs) π ∧ Integrable (Xi m δF η πs) πs ∧
      ∫ z, Xi m δF η πs z ∂πs ≤ ∫ z, Xi m δF η πs z ∂π := by sorry

end GameRandEnv.FirstOrder
