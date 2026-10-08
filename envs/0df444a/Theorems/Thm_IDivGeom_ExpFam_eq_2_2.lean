-- Prove2me | Theorems.Thm_IDivGeom_ExpFam_eq_2_2
-- name    : IDivGeom.ExpFam.eq_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T16:58:21.584651+00:00
-- url     : https://prove2.me/theorems/360443bb-7197-47d1-8715-4bc468031b45
-- title:
--   (2.2) — parallelogram identity for I-divergence
-- statement:
--   Let $P, P', R$ be probability distributions on $(X,\mathcal X)$ with $I(P\|R)<\infty$ and $I(P'\|R)<\infty$, and let $M=\frac{P+P'}{2}$ be their midpoint. Then
--   $$I(P\|R)+I(P'\|R) = 2\,I\Big(\tfrac{P+P'}{2}\Big\|R\Big) + I\Big(P\Big\|\tfrac{P+P'}{2}\Big) + I\Big(P'\Big\|\tfrac{P+P'}{2}\Big).$$
--
--   This is the analogue, for I-divergence, of the parallelogram identity of Euclidean geometry, with I-divergence in the role of squared distance. In the proof of Theorem 2.1 it shows that along a minimizing sequence in a convex set the divergences of the terms from their midpoints tend to zero.
--
--   **Formalization Note** The page states (2.2) for two members $P_m, P_n$ of a sequence with $I(P_n\|R)<\infty$; here they are renamed $P, P'$ and the finiteness hypotheses are kept. The identity is an equation in $[0,\infty]$ (`klDiv`); under the hypotheses every term is finite.
-- source:
--   Csiszár, I-divergence geometry of probability distributions and minimization problems, Ann. Probab. 3 (1975), p. 148 (PDF 3), (2.2), proof of Theorem 2.1

import Mathlib
import Definitions.Def_IDivGeom_ExpFam_Setting

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal NNReal

namespace IDivGeom.ExpFam

theorem eq_2_2 {X : Type*} [MeasurableSpace X]
    (P P' R : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    [IsProbabilityMeasure R] (hP : klDiv P R ≠ ⊤) (hP' : klDiv P' R ≠ ⊤) :
    klDiv P R + klDiv P' R =
      2 * klDiv ((1 / 2 : ℝ≥0∞) • (P + P')) R
        + klDiv P ((1 / 2 : ℝ≥0∞) • (P + P'))
        + klDiv P' ((1 / 2 : ℝ≥0∞) • (P + P')) := by sorry

end IDivGeom.ExpFam
