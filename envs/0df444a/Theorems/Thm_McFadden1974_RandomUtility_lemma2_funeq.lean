-- Prove2me | Theorems.Thm_McFadden1974_RandomUtility_lemma2_funeq
-- name    : McFadden1974.RandomUtility.lemma2_funeq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:44:13.709902+00:00
-- url     : https://prove2.me/theorems/aec4788e-969b-4173-b61c-539dd80bfc53
-- title:
--   Lemma 2, proof — the functional equation $G(v - \log K) = G(v)^K$
-- statement:
--   Suppose the taste shocks are i.i.d. with a translation complete law $\mu$ whose distribution function is $G$, and fix a universe $X$ with a surjective utility map $u:X\to\mathbb R$, and suppose the selection probabilities are logit on every finite subset of $X$. Then for every positive integer $K$ and every real $v$,
--   $$
--   G(v - \log K) = G(v)^K.
--   $$
--
--   In the proof of Lemma 2 this identity comes from comparing a choice between one alternative and $K$ identical alternatives with a binary choice against a single alternative whose utility is larger by $\log K$; it is the functional equation from which the extreme value form of $G$ is derived.
--
--   **Formalization Note** The identity holds at every $v$, not only almost every $v$.
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 112, Lemma 2, proof (PDF p. 8)

import Mathlib
import Definitions.Def_McFadden1974_RandomUtility_Model

open MeasureTheory ProbabilityTheory Finset

namespace McFadden1974.RandomUtility

/-- **Lemma 2, proof — the functional equation** (McFadden, Conditional Logit Analysis of
Qualitative Choice Behavior, in Frontiers in Econometrics (1974), p. 112, Lemma 2, proof; PDF
p. 8): comparing (14) and (15), "this can be true for all values of `v_x ∈ (−∞, +∞)` only if the
term in brackets is zero, since G is translation complete, implying `G(v_x − log K) = G(v_x)^K`."

Under the hypotheses of Lemma 2 — a surjective utility map `u : X → ℝ`, i.i.d. shocks with a
translation complete law `μ`, and (12) on all finite subsets of `X` — `G = cdf μ` satisfies
`G(v − log K) = G(v)^K` for every positive integer `K` and every real `v`.

Formalization Note: `K` is a positive natural number, so `Real.log K` has positive argument.
The paper's proof selects `K` distinct alternatives with equal utility; surjectivity alone does
not guarantee this selection. The statement retains the paper's hypothesis, and the identity
is stated for every `v`, not almost every `v`. -/
theorem lemma2_funeq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {X : Type*} (u : X → ℝ) (hu : Function.Surjective u)
    (hTC : TranslationComplete μ) (h12 : IsLogitOn μ u)
    (K : ℕ) (hK : 0 < K) (v : ℝ) :
    cdf μ (v - Real.log K) = cdf μ v ^ K := by sorry

end McFadden1974.RandomUtility
