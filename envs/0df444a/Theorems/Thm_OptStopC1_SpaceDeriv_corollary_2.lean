-- Prove2me | Theorems.Thm_OptStopC1_SpaceDeriv_corollary_2
-- name    : OptStopC1.SpaceDeriv.corollary_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:06.395381+00:00
-- url     : https://prove2.me/theorems/84527947-f939-4f65-ae1c-9869317a0268
-- title:
--   Corollary 2 — probabilistic regularity implies Green regularity
-- statement:
--   Let $D$ be closed and $C=D^c$. If $z\in\partial C$ is probabilistically regular for $D$ and $X$ is strong Feller, then $z$ is Green regular for $D$:
--
--   $$\forall\varepsilon>0,\qquad\lim_{C\ni x\to z}P_x(\tau_D\ge\varepsilon)=0.$$
--
--   The conclusion supplies the short-entry-time behavior needed near the stopping boundary.
-- source:
--   De Angelis & Peskir, Global C¹ Regularity of the Value Function in Optimal Stopping Problems, arXiv:1812.04564v2, p. 9, Corollary 2

import Definitions.Def_OptStopC1_SpaceDeriv_LocalBounds

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace OptStopC1.SpaceDeriv

theorem corollary_2
    {d : ℕ} (hd : 0 < d) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ≥0 mΩ) (X : Flow d Ω)
    (hX : IsStandardMarkovFlow X P 𝔽)
    (D : Set (State d)) (hD : IsClosed D)
    (z : State d) (hz : z ∈ frontier Dᶜ)
    (hPR : IsProbRegular X P D z) (hF : IsStrongFeller X P) :
    IsGreenRegular X P Dᶜ D z := by sorry
end OptStopC1.SpaceDeriv
