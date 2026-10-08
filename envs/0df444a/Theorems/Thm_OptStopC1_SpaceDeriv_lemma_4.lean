-- Prove2me | Theorems.Thm_OptStopC1_SpaceDeriv_lemma_4
-- name    : OptStopC1.SpaceDeriv.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:08.300856+00:00
-- url     : https://prove2.me/theorems/50d410b4-a550-433c-bce8-a604b72a3d36
-- title:
--   Lemma 4 — upper semicontinuity for the interior hitting time
-- statement:
--   Let $D$ be closed. Suppose that for each fixed $t\ge0$, the spatial map $x\mapsto X_t^x$ is continuous almost surely. Then, for every $\varepsilon>0$,
--
--   $$x\longmapsto P_x(\sigma_{D^\circ}\ge\varepsilon)\quad\text{is upper semicontinuous on }\mathbb R^d.$$
--
--   This gives the alternative regularity route when strong Feller continuity is unavailable. The flow remains a standard Markov flow under the standing model.
-- source:
--   De Angelis & Peskir, Global C¹ Regularity of the Value Function in Optimal Stopping Problems, arXiv:1812.04564v2, p. 10, Lemma 4, equations (3.5)–(3.6)

import Definitions.Def_OptStopC1_SpaceDeriv_LocalBounds

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace OptStopC1.SpaceDeriv

theorem lemma_4
    {d : ℕ} (hd : 0 < d) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ≥0 mΩ) (X : Flow d Ω)
    (hX : IsStandardMarkovFlow X P 𝔽)
    (D : Set (State d)) (hD : IsClosed D)
    (hcont : FlowContinuousAE X P) (ε : ℝ≥0) (hε : 0 < ε) :
    UpperSemicontinuous
      (fun x : State d => P {ω | (ε : ℝ≥0∞) ≤ hittingTime X x (interior D) ω}) := by sorry
end OptStopC1.SpaceDeriv
