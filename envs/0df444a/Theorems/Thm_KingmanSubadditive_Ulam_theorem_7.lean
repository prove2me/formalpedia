-- Prove2me | Theorems.Thm_KingmanSubadditive_Ulam_theorem_7
-- name    : KingmanSubadditive.Ulam.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:45:53.953987+00:00
-- url     : https://prove2.me/theorems/3abfdb65-d733-49bf-b996-774e518e8c2b
-- title:
--   Theorem 7 (Hammersley) — n^{−½} l(π_n) converges in probability to an absolute constant c
-- statement:
--   Let $\pi_n$ be a random permutation uniformly distributed over the group $\mathcal S_n$ of permutations of $\{1,\dots,n\}$, and let $l(\pi_n)$ be the length of its longest ascending sequence. Then there is an absolute constant $c$ such that, as $n\to\infty$,
--   $$n^{-1/2}\,l(\pi_n)\ \longrightarrow\ c\qquad\text{in probability},$$
--   that is, $P\{|n^{-1/2}l(\pi_n)-c|>\varepsilon\}\to0$ for every $\varepsilon>0$.
--
--   This is Hammersley's answer to the existence part of Ulam's problem; the constant $c$ is the one bounded in Theorem 8.
--
--   **Formalization Note** "Absolute" means that $c$ depends on nothing; the existential quantifier is outermost. Probabilities are proportions of the $n!$ permutations.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 895, Theorem 7

import Mathlib
import Definitions.Def_KingmanSubadditive_Ulam_Permutations

namespace KingmanSubadditive.Ulam

/-- **Theorem 7 (Hammersley)** (Kingman, *Subadditive ergodic theory*, Ann. Probab.
1(6):883–899 (1973), §2.4, p. 895). Let `π_n` be a random permutation uniformly distributed over
`𝒮_n`. Then, as `n → ∞`, `n^{−½} l(π_n)` converges in probability to an absolute constant `c`.

**Formalization Note** "Absolute" means `c` depends on nothing, so `∃ c` is outermost. -/
theorem theorem_7 : ∃ c : ℝ, ConvergesInProbUniform c := by sorry

end KingmanSubadditive.Ulam
