-- Prove2me | Theorems.Thm_OptStopC1_SpaceDeriv_lemma_1
-- name    : OptStopC1.SpaceDeriv.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:07.903017+00:00
-- url     : https://prove2.me/theorems/48bf0186-60da-4ad8-b3f3-e511f46213d7
-- title:
--   Lemma 1 — upper semicontinuity of the delayed hitting probability
-- statement:
--   Let $D\subseteq\mathbb R^d$ be closed and let $X$ be a standard Markov flow. If $X$ is strong Feller, then for every $\varepsilon>0$,
--
--   $$x\longmapsto P_x(\sigma_D\ge\varepsilon)\quad\text{is upper semicontinuous on }\mathbb R^d.$$
--
--   This is the first link from strong Feller continuity to boundary regularity. The hitting time is the first strictly positive time in $D$.
-- source:
--   De Angelis & Peskir, Global C¹ Regularity of the Value Function in Optimal Stopping Problems, arXiv:1812.04564v2, p. 9, Lemma 1, equation (3.1)

import Definitions.Def_OptStopC1_SpaceDeriv_LocalBounds

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace OptStopC1.SpaceDeriv

theorem lemma_1
    {d : ℕ} (hd : 0 < d) {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝔽 : Filtration ℝ≥0 mΩ) (X : Flow d Ω)
    (hX : IsStandardMarkovFlow X P 𝔽)
    (D : Set (State d)) (hD : IsClosed D)
    (hF : IsStrongFeller X P) (ε : ℝ≥0) (hε : 0 < ε) :
    UpperSemicontinuous
      (fun x : State d => P {ω | (ε : ℝ≥0∞) ≤ hittingTime X x D ω}) := by sorry
end OptStopC1.SpaceDeriv
