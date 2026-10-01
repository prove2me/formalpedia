-- Prove2me | Theorems.Thm_MurtyKabadi_Reduction_lemma2_optimum_gap
-- name    : MurtyKabadi.Reduction.lemma2_optimum_gap
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:15:47.070869+00:00
-- url     : https://prove2.me/theorems/d014e4fb-c295-41cf-ac93-5aa760a026e8
-- title:
--   Lemma 2 — the optimum of $\min x^{\mathsf T}Dx$ over $[0,1]^m$ is $0$ or at most $-2^{-L}$
-- statement:
--   Let $D$ be an integer symmetric matrix of order $m$, $Q(x) = x^{\mathsf T}Dx$, and let $L$ be the encoding size of $D$. Consider the QP (8):
--   $$\text{minimize } Q(x) \quad \text{subject to } 0 \le x_j \le 1,\ j = 1, \dots, m.$$
--   Its optimal value is either $0$ or at most $-2^{-L}$. Equivalently, either
--   $$Q(x) \ge 0 \text{ for every } x \in [0,1]^m,$$
--   or there is an $x \in [0,1]^m$ with
--   $$Q(x) \le -2^{-L}.$$
--
--   The lemma is the precision bound of the reduction: a quadratic form with integer coefficients that dips below zero on the unit box does so by an amount with only polynomially many bits, which is what lets the reduction subtract a tiny $\varepsilon$ without changing the answer.
--
--   **Formalization Note** The optimum of (8) exists (the box is compact) and is at most $Q(0) = 0$, so "the optimum is $0$ or $\le -2^{-L}$" is stated as the disjunction above, without `sInf`. $L$ is Schrijver's encoding size (`encSize`), since the paper does not define "size". $D$ is taken symmetric: the paper's §4 says "as before, let $D$ be an integer square symmetric matrix", and the LCP (9) used in the proof is the optimality system of (8) only for symmetric $D$.
-- source:
--   Murty and Kabadi, Some NP-complete problems in quadratic and nonlinear programming, Math. Programming 39 (1987), p. 122, Lemma 2

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_QuadraticProblems
import Definitions.Def_MurtyKabadi_Reduction_encSize

namespace MurtyKabadi.Reduction

theorem lemma2_optimum_gap {m : ℕ} (D : Matrix (Fin m) (Fin m) ℤ) (hD : D.IsSymm) :
    (∀ x : Fin m → ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ Q (D.map (Int.cast : ℤ → ℝ)) x) ∨
    ∃ x : Fin m → ℝ, 0 ≤ x ∧ x ≤ 1 ∧
      Q (D.map (Int.cast : ℤ → ℝ)) x ≤ -((2 : ℝ) ^ (-(encSize D : ℤ))) := by sorry

end MurtyKabadi.Reduction
