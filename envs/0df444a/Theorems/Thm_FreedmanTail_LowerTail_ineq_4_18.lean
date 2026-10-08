-- Prove2me | Theorems.Thm_FreedmanTail_LowerTail_ineq_4_18
-- name    : FreedmanTail.LowerTail.ineq_4_18
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:15:45.472775+00:00
-- url     : https://prove2.me/theorems/d8ab88fd-dfa4-48e5-bd63-f7f7ec820a36
-- title:
--   (4.18) — P{W < x} < exp[−a²/(2(a + x))] under (4.11a)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $a>0$, and $W\ge0$ a random variable satisfying (4.11a): $E\{\exp[-e(\lambda)W]\}\le\exp(-\lambda a)$ for every $\lambda\ge0$, where $e(\lambda)=e^\lambda-1-\lambda$. Then for every $x\ge0$
--
--   $$
--   P\{W<x\}<\exp\!\left[-\frac{a^2}{2(a+x)}\right].
--   $$
--
--   This is the left-tail estimate for $W$ that bounds the error terms $\eta_1,\eta_2,\eta_3$ in the proof of Proposition (4.10): the variable $W$ is unlikely to be much smaller than $a$.
--
--   **Formalization Note** The page states (4.18) for the integration variable $x$ of (4.15) without naming its range; it is stated here for every $x\ge 0$, which covers every use on $[0,\infty)$ (at $x=0$ the left side is $0$). Only (4.11a) is assumed.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 110 (PDF p. 11), display (4.18)

import Mathlib
import Definitions.Def_FreedmanTail_LowerTail_Exponents
import Definitions.Def_FreedmanTail_LowerTail_Hypotheses
import Definitions.Def_FreedmanTail_LowerTail_ProofNotation
open MeasureTheory

namespace FreedmanTail.LowerTail

/-- Freedman (1975), (4.18), p. 110: under (4.11a), for every `x ≥ 0`,
`P{W < x} < exp[−a²/(2(a + x))]`. -/
theorem ineq_4_18 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (a : ℝ) (ha : 0 < a)
    (hU : LaplaceUpper P W a) (x : ℝ) (hx : 0 ≤ x) :
    P.real {ω | W ω < x} < Real.exp (-(a ^ 2 / (2 * (a + x)))) := by sorry

end FreedmanTail.LowerTail
