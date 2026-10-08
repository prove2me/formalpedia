-- Prove2me | Theorems.Thm_KingmanSubadditive_Ulam_theorem_8
-- name    : KingmanSubadditive.Ulam.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:46:37.802218+00:00
-- url     : https://prove2.me/theorems/1a0434dc-72eb-4900-ba30-21510a60db49
-- title:
--   Theorem 8 — the Ulam constant satisfies (8/π)^½ ≤ c ≤ δ^½ + δ^{−½}, hence 1.59 < c < 2.49
-- statement:
--   Let $c$ be the constant of (2.4.3), that is, the limit in probability of $n^{-1/2}\,l(\pi_n)$ for $\pi_n$ uniformly distributed over the permutation group $\mathcal S_n$, where $l(\pi_n)$ is the length of the longest ascending sequence (Theorem 7). Let $\delta$ be the unique positive root of
--   $$\log(1+\delta)=\frac{2\delta}{1+\delta},$$
--   and $\beta=\delta^{1/2}+\delta^{-1/2}$. Then
--   $$\Big(\frac8\pi\Big)^{1/2}\ \le\ c\ \le\ \beta, \tag{2.4.4}$$
--   and thus
--   $$1.59<c<2.49. \tag{2.4.5}$$
--
--   These bounds refine Hammersley's earlier bounds $\tfrac12\pi\le c\le e$.
--
--   **Formalization Note** The constant enters as a hypothesis: the statement holds for every real $c$ to which $n^{-1/2}l(\pi_n)$ converges in probability. A limit in probability is unique and Theorem 7 shows it exists, so this is a statement about one number; no sign or bound on $c$ is assumed. The statement also asserts that the positive root $\delta$ exists and is unique, so the upper bound is not vacuous. The $\pi$ in (2.4.4) is the circle constant. (2.4.4) is non-strict and (2.4.5) strict, as printed.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 895, Theorem 8, (2.4.4)–(2.4.5)

import Mathlib
import Definitions.Def_KingmanSubadditive_Ulam_Permutations

namespace KingmanSubadditive.Ulam

/-- **Theorem 8** (Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899 (1973), §2.4,
p. 895). The constant `c` in (2.4.3) satisfies
(2.4.4) `(8/π)^½ ≤ c ≤ β`, where `β = δ^½ + δ^{−½}` and `δ` is the unique positive root of
`log (1 + δ) = 2δ/(1 + δ)`. Thus (2.4.5) `1.59 < c < 2.49`.

**Formalization Note** "The constant `c` in (2.4.3)" is the limit in probability of `n^{−½} l(π_n)`
for `π_n` uniform on `𝒮_n` (Theorem 7); it is taken as the hypothesis `ConvergesInProbUniform c`.
That limit is unique, and Theorem 7 shows it exists, so the statement is about that one number.
No sign or bound on `c` is assumed. The first conjunct asserts that the positive root `δ` exists
and is unique, so the upper bound is not vacuous. `π` in (2.4.4) is `Real.pi`; (2.4.4) is
non-strict and (2.4.5) strict, as printed. -/
theorem theorem_8 (c : ℝ) (hc : ConvergesInProbUniform c) :
    (∃! δ : ℝ, 0 < δ ∧ Real.log (1 + δ) = 2 * δ / (1 + δ)) ∧
    (∀ δ : ℝ, 0 < δ → Real.log (1 + δ) = 2 * δ / (1 + δ) →
      Real.sqrt (8 / Real.pi) ≤ c ∧ c ≤ Real.sqrt δ + 1 / Real.sqrt δ) ∧
    (1.59 : ℝ) < c ∧ c < 2.49 := by sorry

end KingmanSubadditive.Ulam
