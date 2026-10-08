-- Prove2me | Theorems.Thm_IDivGeom_IPFP_lemma_2_1_a
-- name    : IDivGeom.IPFP.lemma_2_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:54:02.062204+00:00
-- url     : https://prove2.me/theorems/bf6efc5b-d580-4f80-bbe5-d73f343b8253
-- title:
--   Lemma 2.1, first part — the segment from P to Q avoids the I-sphere iff ∫ log q_R dP ≥ I(Q‖R)
-- statement:
--   Let $P,Q,R$ be probability distributions with $I(P\|Q)<\infty$ and $I(Q\|R)<\infty$, and let $q_R$ be the $R$-density of $Q$. For $0\le\alpha\le1$ put $P_\alpha=\alpha P+(1-\alpha)Q$. Then the segment joining $P$ and $Q$ does not meet the I-sphere $S(R,\rho)=\{P':I(P'\|R)<\rho\}$ of radius $\rho=I(Q\|R)$, that is,
--
--   $$
--   I(P_\alpha\|R)\ge I(Q\|R)\quad\text{for all }0\le\alpha\le1,
--   $$
--
--   if and only if
--
--   $$
--   \int\log q_R\,dP\ge I(Q\|R).\qquad(2.8)
--   $$
--
--   This is the local criterion from which the characterization of I-projections in Theorem 2.2 is derived.
--
--   **Formalization Note** $I$ is Mathlib's `klDiv`; $\alpha$ ranges over $[0,1]$ as a nonnegative real. $\int\log q_R\,dP$ is the extended-real `logDensInt R Q P` (positive part minus negative part, $\log0=-\infty$). The hypotheses make its negative part finite, so the value is a well-defined element of $(-\infty,+\infty]$.
-- source:
--   Csiszár, I-divergence geometry of probability distributions and minimization problems, Ann. Probab. 3 (1975), p. 149, Lemma 2.1, (2.7)–(2.8) (PDF p. 4)

import Mathlib
import Definitions.Def_IDivGeom_IPFP_Setting

open MeasureTheory InformationTheory
open scoped ENNReal NNReal

namespace IDivGeom.IPFP

theorem lemma_2_1_a {X : Type*} [MeasurableSpace X]
    (P Q R : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [IsProbabilityMeasure R]
    (hPQ : klDiv P Q ≠ ⊤) (hQR : klDiv Q R ≠ ⊤) :
    (∀ α : ℝ≥0, α ≤ 1 →
        klDiv Q R ≤ klDiv ((α : ℝ≥0∞) • P + ((1 - α : ℝ≥0) : ℝ≥0∞) • Q) R) ↔
      ((klDiv Q R : ℝ≥0∞) : EReal) ≤ logDensInt R Q P := by sorry

end IDivGeom.IPFP
