-- Prove2me | Theorems.Thm_NConjecture_n_conjecture
-- name    : NConjecture.n_conjecture
-- status  : Open
-- author  : @LG
-- created : 2026-11-22T00:46:12.726854+00:00
-- url     : https://prove2.me/theorems/ada40e3c-d88d-4248-8615-6e7cb64234eb
-- title:
--   The $n$-conjecture (Browkin–Brzeziński)
-- statement:
--   The **$n$-conjecture** of Browkin and Brzeziński (§2, p. 933), the generalization of the abc conjecture to more than three integers. For every $n\ge 3$ and every $\varepsilon>0$ there exists a constant $C>0$ (depending only on $n$ and $\varepsilon$) such that every admissible $n$-tuple of integers $a=(a_1,\dots,a_n)$ — satisfying $a_1+\cdots+a_n=0$, $\gcd(a_1,\dots,a_n)=1$, and no nonempty proper subsum equal to $0$ — obeys
--   $$\max_{1\le i\le n}|a_i|\ \le\ C\,\operatorname{rad}(a_1\cdots a_n)^{\,2n-5+\varepsilon}.$$
--   Equivalently, $\limsup\{L_n\}=2n-5$ where $L_n=\log\max_i|a_i|/\log\operatorname{rad}(a_1\cdots a_n)$ ranges over all admissible $n$-tuples; the lower bound $\limsup\{L_n\}\ge 2n-5$ is their proved Theorem 1, so the content of the goal is the upper bound. The case $n=3$ is the abc conjecture, and every case $n\ge 4$ implies abc.
--
--   **Formalization Note.** The goal is `∀ n ≥ 3, conjAt n`, with `conjAt` and `admissible` from `NConjecture_Defs`. The radical reuses `Brocard.radical`; the exponent $2n-5+\varepsilon$ is real arithmetic.
-- source:
--   J. Browkin, J. Brzeziński, Some remarks on the abc-conjecture, Math. Comp. 62(206) (1994), 931–939. https://cr.yp.to/bib/1994/browkin.pdf §2 p. 933 (the n-conjecture, conditions (i)–(iii), limsup = 2n−5). ε-form: M. Waldschmidt, Lecture on the abc conjecture and some of its consequences, Proc. Math. Stat. 98 (2015), 211–230. https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/abcLahoreProceedings.pdf

import Mathlib
import Definitions.Def_NConjecture_Defs

namespace NConjecture

theorem n_conjecture (n : ℕ) (hn : 3 ≤ n) : conjAt n := by sorry

end NConjecture
