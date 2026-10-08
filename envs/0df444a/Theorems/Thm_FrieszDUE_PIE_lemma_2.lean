-- Prove2me | Theorems.Thm_FrieszDUE_PIE_lemma_2
-- name    : FrieszDUE.PIE.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T07:18:59.653686+00:00
-- url     : https://prove2.me/theorems/436e6ab5-ec23-41ba-89bc-3481be4265c1
-- title:
--   Lemma 2, p. 187 — ν{t ∈ S: f(t) > 0} > 0 implies ν{t ∈ S: f(t) > ε} > 0 for all ε ∈ [0, ε₀], some ε₀ > 0
-- statement:
--   Let $T\in\mathbb R$, let $\nu$ be Lebesgue measure on $[0,T]$, let $S\subseteq[0,T]$ with $\nu(S)>0$, and let $f$ be a measurable real function with $\nu\{t\in S: f(t)>0\}>0$. Then there is $\varepsilon_0>0$ such that
--
--   $$\nu\{t\in S: f(t)>\varepsilon\}>0\qquad\text{for all }\varepsilon\in[0,\varepsilon_0].$$
--
--   This elementary property of measurable functions is used twice in the sufficiency half of Theorem 2, to pass from a set of positive measure on which a quantity is positive to one on which it exceeds a fixed positive margin.
--
--   **Formalization Note** $S$ is an arbitrary set (its measure is the outer measure); the paper does not require $S$ measurable in the statement, and the claim holds without it.
-- source:
--   Friesz, Bernstein, Smith, Tobin and Wie, A variational inequality formulation of the dynamic network user equilibrium problem, Oper. Res. 41 (1993), p. 187, Lemma 2

import Mathlib
import Definitions.Def_FrieszDUE_PIE_Setting

namespace FrieszDUE.PIE

open MeasureTheory

/-- Lemma 2, p. 187. -/
theorem lemma_2 (T : ℝ) (S : Set ℝ) (hS : S ⊆ Set.Icc 0 T) (hSpos : 0 < ν T S)
    (f : ℝ → ℝ) (hf : Measurable f) (hpos : 0 < ν T {t | t ∈ S ∧ 0 < f t}) :
    ∃ ε₀ > 0, ∀ ε ∈ Set.Icc (0 : ℝ) ε₀, 0 < ν T {t | t ∈ S ∧ ε < f t} := by sorry

end FrieszDUE.PIE
