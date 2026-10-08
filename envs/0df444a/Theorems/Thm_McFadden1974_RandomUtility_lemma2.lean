-- Prove2me | Theorems.Thm_McFadden1974_RandomUtility_lemma2
-- name    : McFadden1974.RandomUtility.lemma2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:44:24.710612+00:00
-- url     : https://prove2.me/theorems/b95ca961-7b34-487e-a1f6-e72eb79d9f81
-- title:
--   Lemma 2 — translation complete i.i.d. shocks giving logit probabilities are extreme value
-- statement:
--   Suppose the taste shocks $\varepsilon_1,\dots,\varepsilon_J$ of the random utility model are independent and identically distributed with a translation complete law whose distribution function is $G$, Fix a universe $X$ and a surjective representative utility map $u:X\to\mathbb R$. Suppose that on every finite subset $B\subseteq X$, the probability of choosing $i\in B$ is $e^{u(i)}/\sum_{j\in B}e^{u(j)}$. Then there is $\alpha > 0$ with
--   $$
--   G(\varepsilon) = e^{-\alpha \exp(-\varepsilon)} \qquad \text{for all real } \varepsilon,
--   $$
--   and if moreover $G(0) = e^{-1}$, then $G(\varepsilon) = e^{-e^{-\varepsilon}}$, the extreme value distribution (13).
--
--   Together with Lemma 1 this shows that, among translation complete shock distributions, the extreme value family is exactly the one producing the conditional logit model.
--
--   **Formalization Note** The statement retains the paper's surjectivity and finite alternative sets. The proof uses $K$ alternatives with equal utility, which surjectivity alone does not supply; this gap needs a separate argument. "Satisfy Equation (3)" is read as: the selection probabilities are those of (2) with i.i.d. shocks; no density is assumed. The parameter $\alpha$ is existential (it equals $-\log G(0)$).
-- source:
--   McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in P. Zarembka (ed.), Frontiers in Econometrics, Academic Press (1974), p. 112, Lemma 2 (PDF p. 8)

import Mathlib
import Definitions.Def_McFadden1974_RandomUtility_Model

open MeasureTheory ProbabilityTheory Finset

namespace McFadden1974.RandomUtility

/-- **Lemma 2** (McFadden, Conditional Logit Analysis of Qualitative Choice Behavior, in Frontiers
in Econometrics (1974), p. 112, Lemma 2; PDF p. 8): if the selection probabilities are given by
(12) and satisfy (3) with independently identically distributed `ε(s, x_i)` having a translation
complete cumulative distribution function `G`, then `G(ε) = e^{−α exp(−ε)}` for a positive
parameter `α`; fixing `α` by `G(0) = e^{−1}` yields the distribution (13).

Formalization Note: `u : X → ℝ` fixes the measured-attribute vector `s`; its surjectivity is
the paper's `v(s, X) = ℝ`. `IsLogitOn μ u` quantifies over injectively enumerated finite subsets
of `X`, including those whose distinct alternatives have equal representative utility.
"Satisfy Equation (3)" is read as the selection probabilities (2) for i.i.d. shocks; no
density is assumed. The paper's positive parameter is existentially quantified. -/
theorem lemma2 (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {X : Type*} (u : X → ℝ) (hu : Function.Surjective u)
    (hTC : TranslationComplete μ) (h12 : IsLogitOn μ u) :
    (∃ α : ℝ, 0 < α ∧ ∀ e : ℝ, cdf μ e = Real.exp (-α * Real.exp (-e))) ∧
    (cdf μ 0 = Real.exp (-1) → IsExtremeValue μ) := by sorry

end McFadden1974.RandomUtility
