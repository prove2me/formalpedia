-- Prove2me | Theorems.Thm_OptStopC1_SpaceDeriv_corollary_5
-- name    : OptStopC1.SpaceDeriv.corollary_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:23.331898+00:00
-- url     : https://prove2.me/theorems/f70c0039-032d-40ad-9476-f9872316e499
-- title:
--   Corollary 5 — Green regularity for the interior and stopping set
-- statement:
--   Let $D$ be closed and $C=D^c$. If $z\in\partial C$ is probabilistically regular for $D^\circ$ and the spatial continuity condition (3.5) holds, then $z$ is Green regular for both $D^\circ$ and $D$:
--
--   $$\lim_{C\ni x\to z}P_x(\tau_{D^\circ}\ge\varepsilon)=\lim_{C\ni x\to z}P_x(\tau_D\ge\varepsilon)=0\qquad(\varepsilon>0).$$
--
--   The interior-set result is stronger and implies the result for $D$.
-- source:
--   De Angelis & Peskir, Global C¹ Regularity of the Value Function in Optimal Stopping Problems, arXiv:1812.04564v2, p. 10, Corollary 5

import Definitions.Def_OptStopC1_SpaceDeriv_LocalBounds

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace OptStopC1.SpaceDeriv

theorem corollary_5
    {d : ℕ} (hd : 0 < d) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ≥0 mΩ) (X : Flow d Ω)
    (hX : IsStandardMarkovFlow X P 𝔽)
    (D : Set (State d)) (hD : IsClosed D)
    (z : State d) (hz : z ∈ frontier Dᶜ)
    (hPR : IsProbRegular X P (interior D) z)
    (hcont : FlowContinuousAE X P) :
    IsGreenRegular X P Dᶜ (interior D) z ∧
    IsGreenRegular X P Dᶜ D z := by sorry
end OptStopC1.SpaceDeriv
