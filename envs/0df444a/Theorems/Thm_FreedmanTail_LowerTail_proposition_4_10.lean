-- Prove2me | Theorems.Thm_FreedmanTail_LowerTail_proposition_4_10
-- name    : FreedmanTail.LowerTail.proposition_4_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:22:49.418985+00:00
-- url     : https://prove2.me/theorems/09ac6bfc-c28c-4d2d-9cd1-b397ffbdf667
-- title:
--   (4.10) Proposition — Laplace bounds (4.11) on W ≥ 0 give P{W < b} > ½ exp[−(½ + 2δ)a²/b]
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $a>0$, and $W$ a nonnegative random variable. Write $e(\lambda)=e^\lambda-1-\lambda$ and $f(\lambda)=e^{-\lambda}-1+\lambda$. Suppose that for all $\lambda\ge0$
--
--   $$
--   E\{\exp[-e(\lambda)W]\}\le\exp(-\lambda a)\qquad\text{(4.11a)}
--   $$
--   $$
--   E\{\exp[-f(\lambda)W]\}\ge\exp(-\lambda(a+1)).\qquad\text{(4.11b)}
--   $$
--
--   Let $\delta,a,b$ be positive with $\delta<\tfrac13$, $b/a>9/\delta^2$ and $a^2/b>(16/\delta^2)\log(64/\delta^2)$ (4.12a–c). Then
--
--   $$
--   P\{W<b\}>\frac12\exp\!\left[-\left(\frac12+2\delta\right)\frac{a^2}{b}\right].\qquad\text{(4.13)}
--   $$
--
--   Applied to the conditional variance $W_a$ that a martingale with increments bounded by $1$ spends before crossing level $a$, this lower bound has the exponent $a^2/(2b)$ of the upper bound $\exp[-a^2/2(a+b)]$ of Theorem (4.1), up to the term $2\delta a^2/b$; it is the analytic core of Freedman's estimate (1.10) of $P\{W_a<b\}$ from below.
--
--   **Formalization Note** The page says "For each $a>0$, let $W_a$ be a nonnegative random variable"; the hypotheses and the conclusion use only the one variable $W_a$ at the one level $a$ of (4.12), so the statement is made for a fixed $a$ and a single $W$ (this implies the printed statement for every member of the family). $W$ is real valued and measurable; real values lose nothing, because (4.11b) with $\lambda\to0$ forces $W<\infty$ almost surely. The expectations are Bochner integrals of functions with values in $(0,1]$, hence genuine.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 109 (PDF p. 10), (4.10) Proposition, displays (4.11a)–(4.13)

import Mathlib
import Definitions.Def_FreedmanTail_LowerTail_Exponents
import Definitions.Def_FreedmanTail_LowerTail_Hypotheses
open MeasureTheory

namespace FreedmanTail.LowerTail

/-- Freedman (1975), (4.10) Proposition, p. 109. Let `W ≥ 0` be a random variable and `a > 0`
with, for all `λ ≥ 0`, (4.11a) `E{exp[−e(λ)W]} ≤ exp(−λa)` and (4.11b)
`E{exp[−f(λ)W]} ≥ exp(−λ(a + 1))`. Let `δ, a, b > 0` satisfy (4.12a)–(4.12c). Then (4.13)
`P{W < b} > ½ exp[−(½ + 2δ)a²/b]`. -/
theorem proposition_4_10 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (δ a b : ℝ)
    (hU : LaplaceUpper P W a) (hL : LaplaceLower P W a) (hpar : ParamConditions δ a b) :
    1 / 2 * Real.exp (-((1 / 2 + 2 * δ) * a ^ 2 / b)) < P.real {ω | W ω < b} := by sorry

end FreedmanTail.LowerTail
