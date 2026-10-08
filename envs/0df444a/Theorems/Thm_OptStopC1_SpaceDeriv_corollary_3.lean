-- Prove2me | Theorems.Thm_OptStopC1_SpaceDeriv_corollary_3
-- name    : OptStopC1.SpaceDeriv.corollary_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:32:59.832449+00:00
-- url     : https://prove2.me/theorems/d7fd46ba-8494-475b-8476-daa1298ca8e7
-- title:
--   Corollary 3 — convergence in probability of entry times
-- statement:
--   Let $D$ be closed and $C=D^c$. Suppose $z\in\partial C$ is probabilistically regular for $D$ and $X$ is strong Feller. For every sequence $x_n\in C$ with $x_n\to z$,
--
--   $$\tau_D^{x_n}\longrightarrow 0\quad\text{in probability}.$$
--
--   Equivalently, $P_{x_n}(\tau_D\ge\varepsilon)\to0$ for every $\varepsilon>0$. This is the strong Feller branch used by Theorem 8.
-- source:
--   De Angelis & Peskir, Global C¹ Regularity of the Value Function in Optimal Stopping Problems, arXiv:1812.04564v2, p. 9, Corollary 3

import Definitions.Def_OptStopC1_SpaceDeriv_LocalBounds

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace OptStopC1.SpaceDeriv

theorem corollary_3
    {d : ℕ} (hd : 0 < d) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ≥0 mΩ) (X : Flow d Ω)
    (hX : IsStandardMarkovFlow X P 𝔽)
    (D : Set (State d)) (hD : IsClosed D)
    (z : State d) (hz : z ∈ frontier Dᶜ)
    (hPR : IsProbRegular X P D z) (hF : IsStrongFeller X P)
    (xs : ℕ → State d) (hxs : ∀ n, xs n ∈ Dᶜ)
    (hconv : Tendsto xs atTop (𝓝 z))
    (ε : ℝ≥0) (hε : 0 < ε) :
    Tendsto (fun n => P {ω | (ε : ℝ≥0∞) ≤ entryTime X (xs n) D ω})
      atTop (𝓝 0) := by sorry
end OptStopC1.SpaceDeriv
