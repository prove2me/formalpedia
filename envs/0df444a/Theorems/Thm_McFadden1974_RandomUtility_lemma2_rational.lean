-- Prove2me | Theorems.Thm_McFadden1974_RandomUtility_lemma2_rational
-- name    : McFadden1974.RandomUtility.lemma2_rational
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:44:16.093402+00:00
-- url     : https://prove2.me/theorems/9771af56-ebdd-460b-a45c-30637b942abc
-- title:
--   Lemma 2, proof — $G(\log(K/L)) = e^{-\alpha L/K}$ with $\alpha = -\log G(0) > 0$
-- statement:
--   Under the hypotheses of Lemma 2 (i.i.d. taste shocks with a translation complete law whose distribution function is $G$, and logit selection probabilities on every finite subset of a universe $X$ whose utility map is onto $\mathbb R$), put $\alpha = -\log G(0)$. Then $\alpha > 0$, and for all positive integers $K$ and $L$,
--   $$
--   G\big(\log (K/L)\big) = e^{-\alpha L/K}.
--   $$
--
--   This determines $G$ on the dense set $\{\log q : q \in \mathbb{Q},\, q > 0\}$; monotonicity of $G$ then extends the formula to the whole real line in Lemma 2.
--
--   **Formalization Note** The claim $\alpha > 0$ includes $0 < G(0) < 1$, so the logarithm is taken of a number in $(0,1)$.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 112, Lemma 2, proof (PDF p. 8)

import Mathlib
import Definitions.Def_McFadden1974_RandomUtility_Model

open MeasureTheory ProbabilityTheory Finset

namespace McFadden1974.RandomUtility

/-- **Lemma 2, proof — values at `log(K/L)`** (McFadden, Conditional Logit Analysis of Qualitative
Choice Behavior, in Frontiers in Econometrics (1974), p. 112, Lemma 2, proof; PDF p. 8):
"Taking `v_x = 0` implies `G(−log K) = e^{−αK}`, where `α = −log G(0) > 0`, and taking
`v_x = log K − log L` implies `G(−log L) = G(log K/L)^K`. Hence, `G(log K/L) = e^{−αL/K}` for all
positive integers K, L."

Under the hypotheses of Lemma 2, including a surjective utility map on the universe of
alternatives, with `α = −log G(0)`, `α > 0` and
`G(log(K/L)) = e^{−αL/K}` for all positive integers `K, L`.

Formalization Note: `α` is written out as `-Real.log (cdf μ 0)`. Since `Real.log` is `0` on
non-positive arguments and at `1`, the conjunct `0 < α` asserts in particular
`0 < G(0) < 1`. `K / L` is the real quotient of the casts, which is positive. -/
theorem lemma2_rational (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {X : Type*} (u : X → ℝ) (hu : Function.Surjective u)
    (hTC : TranslationComplete μ) (h12 : IsLogitOn μ u) :
    0 < -Real.log (cdf μ 0) ∧
    ∀ K L : ℕ, 0 < K → 0 < L →
      cdf μ (Real.log ((K : ℝ) / L)) = Real.exp (-(-Real.log (cdf μ 0)) * L / K) := by sorry

end McFadden1974.RandomUtility
