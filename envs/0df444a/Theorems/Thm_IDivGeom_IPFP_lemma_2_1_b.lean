-- Prove2me | Theorems.Thm_IDivGeom_IPFP_lemma_2_1_b
-- name    : IDivGeom.IPFP.lemma_2_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:54:44.500117+00:00
-- url     : https://prove2.me/theorems/c98dcc2e-7240-407c-92fb-0bf3185c7d32
-- title:
--   Lemma 2.1, second part — if Q is an inner point of the segment from P to P′, the segment avoids the I-sphere iff ∫ log q_R dP = I(Q‖R)
-- statement:
--   Let $P,P',Q,R$ be probability distributions and $0<\alpha<1$ with
--
--   $$
--   Q=\alpha P+(1-\alpha)P'.\qquad(2.9)
--   $$
--
--   Let $q_R$ be the $R$-density of $Q$. If $I(Q\|R)<\infty$, then $I(P\|R)<\infty$, and the segment $\{\beta P+(1-\beta)P':0\le\beta\le1\}$ does not meet the I-sphere $S(R,\rho)$ with $\rho=I(Q\|R)$, that is, $I(\beta P+(1-\beta)P'\|R)\ge I(Q\|R)$ for all $0\le\beta\le1$, if and only if
--
--   $$
--   \int\log q_R\,dP=I(Q\|R).\qquad(2.10)
--   $$
--
--   This equality version is what makes the Pythagorean identity exact at algebraic inner points (Theorem 2.2) and in the proof of Theorem 3.1.
--
--   **Formalization Note** $I$ is Mathlib's `klDiv`; $\alpha,\beta$ are nonnegative reals. "Does not intersect $S(R,\rho)$" is written out as the inequality for every point of the segment, as the paper does in the first part of the lemma. $\int\log q_R\,dP$ is the extended-real `logDensInt R Q P` with $\log0=-\infty$.
-- source:
--   Csiszár, I-divergence geometry of probability distributions and minimization problems, Ann. Probab. 3 (1975), p. 149, Lemma 2.1, (2.9)–(2.10) (PDF p. 4)

import Mathlib
import Definitions.Def_IDivGeom_IPFP_Setting

open MeasureTheory InformationTheory
open scoped ENNReal NNReal

namespace IDivGeom.IPFP

theorem lemma_2_1_b {X : Type*} [MeasurableSpace X]
    (P P' Q R : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1)
    (h29 : Q = (α : ℝ≥0∞) • P + ((1 - α : ℝ≥0) : ℝ≥0∞) • P')
    (hQR : klDiv Q R ≠ ⊤) :
    klDiv P R ≠ ⊤ ∧
      ((∀ β : ℝ≥0, β ≤ 1 →
          klDiv Q R ≤ klDiv ((β : ℝ≥0∞) • P + ((1 - β : ℝ≥0) : ℝ≥0∞) • P') R) ↔
        logDensInt R Q P = ((klDiv Q R : ℝ≥0∞) : EReal)) := by sorry

end IDivGeom.IPFP
