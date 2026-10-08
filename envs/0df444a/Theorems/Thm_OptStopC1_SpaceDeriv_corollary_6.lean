-- Prove2me | Theorems.Thm_OptStopC1_SpaceDeriv_corollary_6
-- name    : OptStopC1.SpaceDeriv.corollary_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:26.656965+00:00
-- url     : https://prove2.me/theorems/75467957-314d-4a16-9338-96007b8d84e0
-- title:
--   Corollary 6 — almost sure convergence of entry times
-- statement:
--   Let $D$ be closed and $C=D^c$. If $z\in\partial C$ is probabilistically regular for $D^\circ$ and (3.5) holds, then for every sequence $x_n\in C$ converging to $z$,
--
--   $$\tau_{D^\circ}^{x_n}\to0\quad\text{almost surely},\qquad\tau_D^{x_n}\to0\quad\text{almost surely}.$$
--
--   The almost sure conclusion is the spatial-flow branch used in Theorem 8 and can be reused for finite-horizon statements.
-- source:
--   De Angelis & Peskir, Global C¹ Regularity of the Value Function in Optimal Stopping Problems, arXiv:1812.04564v2, p. 11, Corollary 6

import Definitions.Def_OptStopC1_SpaceDeriv_LocalBounds

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace OptStopC1.SpaceDeriv

theorem corollary_6
    {d : ℕ} (hd : 0 < d) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ≥0 mΩ) (X : Flow d Ω)
    (hX : IsStandardMarkovFlow X P 𝔽)
    (D : Set (State d)) (hD : IsClosed D)
    (z : State d) (hz : z ∈ frontier Dᶜ)
    (hPR : IsProbRegular X P (interior D) z)
    (hcont : FlowContinuousAE X P)
    (xs : ℕ → State d) (hxs : ∀ n, xs n ∈ Dᶜ)
    (hconv : Tendsto xs atTop (𝓝 z)) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n => entryTime X (xs n) (interior D) ω) atTop (𝓝 0) ∧
      Tendsto (fun n => entryTime X (xs n) D ω) atTop (𝓝 0) := by sorry
end OptStopC1.SpaceDeriv
