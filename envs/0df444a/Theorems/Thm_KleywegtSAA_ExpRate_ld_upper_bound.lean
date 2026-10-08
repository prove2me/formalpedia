-- Prove2me | Theorems.Thm_KleywegtSAA_ExpRate_ld_upper_bound
-- name    : KleywegtSAA.ExpRate.ld_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T00:03:52.764984+00:00
-- url     : https://prove2.me/theorems/2cd25682-938a-4466-a298-90a0c2cccccb
-- title:
--   §2.2, (2.4), p. 3 — (1/N) log P(Z_N ≥ a) ≤ −I(a)
-- statement:
--   Let $X_1, X_2, \dots$ be independent, identically distributed real random variables on a probability space $(\Omega, P)$, distributed as $X$, and let $Z_N = N^{-1}\sum_{i=1}^N X_i$. Let $\Lambda(t) = \log \mathbb E\, e^{tX} \in (-\infty, +\infty]$ and $I(z) = \sup_{t \ge 0}\{tz - \Lambda(t)\}$. Then for every $N \ge 1$ and every real $a$,
--   $$\frac1N \log P(Z_N \ge a) \le -I(a),$$
--   with the convention $\log 0 = -\infty$.
--
--   This is the upper bound of Cramér's large-deviations theorem in non-asymptotic form; it holds without any moment assumption on $X$.
--
--   **Formalization Note** The inequality is in the extended reals: $\log$ of a probability is `ENNReal.log`, with $\log 0 = -\infty$, and $I(a)$ may be $+\infty$ (then $-I(a) = -\infty$ and the claim is $P(Z_N \ge a) = 0$). The sequence is $0$-indexed: $X_i$ is the $(i-1)$-st term and $X$ is the first term.
-- source:
--   Kleywegt & Shapiro, The sample average approximation method for stochastic discrete optimization, preprint (two-author version, sha256 56657748…), p. 3, (2.4) and the definition of I(z) below it

import Mathlib
import Definitions.Def_KleywegtSAA_ExpRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace KleywegtSAA.ExpRate

/-- The large-deviations upper bound (2.4), p. 3: for an i.i.d. real sequence with sample average
`Z_N`, every `N ≥ 1` and every real `a`, `(1/N) log P(Z_N ≥ a) ≤ −I(a)`, with `log 0 = −∞`. -/
theorem ld_upper_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hYm : ∀ i, Measurable (Y i)) (hind : iIndepFun Y P)
    (hid : ∀ i, IdentDistrib (Y i) (Y 0) P P) :
    ∀ N : ℕ, 1 ≤ N → ∀ a : ℝ,
      ((1 / (N : ℝ) : ℝ) : EReal) * ENNReal.log (P {ω | a ≤ sampleMean Y N ω}) ≤
        - rateFn P (Y 0) a := by sorry

end KleywegtSAA.ExpRate
