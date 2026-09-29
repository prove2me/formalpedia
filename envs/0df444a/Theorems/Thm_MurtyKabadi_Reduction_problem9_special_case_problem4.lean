-- Prove2me | Theorems.Thm_MurtyKabadi_Reduction_problem9_special_case_problem4
-- name    : MurtyKabadi.Reduction.problem9_special_case_problem4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:17:15.31864+00:00
-- url     : https://prove2.me/theorems/ccaacc76-210c-472e-98d6-eebd94837f93
-- title:
--   Proof of Theorem 1, p. 125 — Problem 9 is a special case of Problem 4
-- statement:
--   Let $d_0; d_1, \dots, d_n$, $\delta$ and $\varepsilon$ be any data of the reduction and let $M$ be the symmetric $2n \times 2n$ matrix of $f_5$. Then:
--
--   1. for all $y, s \in \mathbb R^n$, with $x = (y, s) \in \mathbb R^{2n}$,
--   $$f_5(y, s) = x^{\mathsf T} M x;$$
--   2. there is $(y,s) \in P$ with $f_5(y,s) < 0$ if and only if Problem 4 for $M$ with $a_0 = n$ has answer "yes", that is, there is $x \ge 0$ in $\mathbb R^{2n}$ with $e^{\mathsf T}x = n$ and $x^{\mathsf T}Mx < 0$.
--
--   This identifies the output of the reduction: the subset sum instance has been turned into an instance $(M, a_0 = n)$ of Problem 4.
--
--   **Formalization Note** The coordinates of $x$ are indexed by `Fin n ⊕ Fin n`, with $x = $ `Sum.elim y s`; then $e^{\mathsf T}x = \sum_j (y_j + s_j)$. No hypothesis on the data is needed.
-- source:
--   Murty and Kabadi, Some NP-complete problems in quadratic and nonlinear programming, Math. Programming 39 (1987), p. 125, proof of Theorem 1, third paragraph (Problem 9 is a special case of Problem 4)

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_QuadraticProblems
import Definitions.Def_MurtyKabadi_Reduction_Construction

namespace MurtyKabadi.Reduction

theorem problem9_special_case_problem4 {n : ℕ} (d : Fin n → ℕ) (d0 δ : ℕ) (ε : ℚ) :
    (∀ y s : Fin n → ℝ, f5 d d0 δ ε y s = Q (mkMatrix d d0 δ ε) (Sum.elim y s)) ∧
    ((∃ p ∈ P n, f5 d d0 δ ε p.1 p.2 < 0) ↔ Problem4 (mkMatrix d d0 δ ε) n) := by sorry

end MurtyKabadi.Reduction
