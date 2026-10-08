-- Prove2me | Theorems.Thm_IDivGeom_IPFP_eq_2_6
-- name    : IDivGeom.IPFP.eq_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:54:04.29732+00:00
-- url     : https://prove2.me/theorems/ab6f6bc4-df05-4852-b398-1b3e1dc1b64e
-- title:
--   Equation (2.6) — the divergence difference equals the integral of log q_R
-- statement:
--   Let $P,Q,R$ be probability distributions (PD's) on a measurable space $(X,\mathcal X)$ with $Q\ll R$, and write $q_R=dQ/dR$ for the $R$-density of $Q$. Let $I(\cdot\|\cdot)$ denote the I-divergence (Kullback–Leibler divergence), with values in $[0,\infty]$. If at least one of $I(P\|Q)$ and $I(P\|R)$ is finite, then
--
--   $$
--   I(P\|R)-I(P\|Q)=\int\log q_R\,dP,
--   $$
--
--   with the conventions $\log 0=-\infty$, $\infty-c=\infty$ and $c-\infty=-\infty$ for finite $c$. In particular, when $I(P\|Q)<\infty$ and $I(P\|R)=\infty$ the right side is $+\infty$, and when $I(P\|R)<\infty$ and $I(P\|Q)=\infty$ it is $-\infty$.
--
--   The identity converts divergence differences into linear functionals of $P$; it underlies Lemma 2.1, Theorem 2.2 and the proof of Theorem 3.1.
--
--   **Formalization Note** $I$ is Mathlib's `klDiv` (valued in $[0,\infty]$). The integral $\int\log q_R\,dP$ is `logDensInt R Q P`: the integral of the positive part of $\log q_R$ minus that of its negative part, computed in the extended reals with `ENNReal.log`, so $\log 0=-\infty$ is kept. Under the hypothesis at most one of the two parts is infinite, so no $\infty-\infty$ occurs. The paper's middle expressions $\int(p_R\log p_R-p_R\log(p_R/q_R))\,dR=\int p_R\log q_R\,dR$ are not stated; the first and last members are.
-- source:
--   Csiszár, I-divergence geometry of probability distributions and minimization problems, Ann. Probab. 3 (1975), p. 149, (2.6) (PDF p. 4)

import Mathlib
import Definitions.Def_IDivGeom_IPFP_Setting

open MeasureTheory InformationTheory
open scoped ENNReal

namespace IDivGeom.IPFP

theorem eq_2_6 {X : Type*} [MeasurableSpace X]
    (P Q R : Measure X) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    [IsProbabilityMeasure R]
    (hQR : Q ≪ R) (hfin : klDiv P Q ≠ ⊤ ∨ klDiv P R ≠ ⊤) :
    ((klDiv P R : ℝ≥0∞) : EReal) - ((klDiv P Q : ℝ≥0∞) : EReal) =
      logDensInt R Q P := by sorry

end IDivGeom.IPFP
