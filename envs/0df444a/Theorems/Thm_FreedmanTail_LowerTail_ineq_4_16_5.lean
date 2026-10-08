-- Prove2me | Theorems.Thm_FreedmanTail_LowerTail_ineq_4_16_5
-- name    : FreedmanTail.LowerTail.ineq_4_16_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:21:38.623993+00:00
-- url     : https://prove2.me/theorems/18dec492-56ab-41a2-8dee-0e090eb4ac16
-- title:
--   (4.16:5) — η_5 < P{W < b} · exp[(−½ + 2δ²)k]
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $W\ge0$ a measurable random variable satisfying (4.11a)–(4.11b) for every $\lambda\ge0$, and let $\delta,a,b$ satisfy (4.12a)–(4.12c). With $\lambda=(1+\delta)a/b$, $\varphi(\lambda)=\lambda^2/2-\lambda^3/6$, $k=a^2/b$ and $I_5=((1-2\delta)b,b]$, let $\eta_5=\varphi(\lambda)\int_{I_5}P\{W<x\}e^{-\varphi(\lambda)x}\,dx$. Then
--
--   $$
--   \eta_5<P\{W<b\}\cdot\exp\!\left[\left(-\tfrac12+2\delta^2\right)k\right].
--   $$
--
--   The term $\eta_5$ is the main term of the proof of Proposition (4.10); this inequality converts the lower bound on $\eta_5$ into the lower bound (4.13) on $P\{W<b\}$.
--
--   **Formalization Note** The strict inequality needs $P\{W<b\}>0$, which holds under the full hypotheses of (4.10); the statement assumes them. The page ends this proof with "This settles (3.16:5)", a misprint for (4.16:5).
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 110 (PDF p. 11), display (4.16:5); proof p. 112

import Mathlib
import Definitions.Def_FreedmanTail_LowerTail_Exponents
import Definitions.Def_FreedmanTail_LowerTail_Hypotheses
import Definitions.Def_FreedmanTail_LowerTail_ProofNotation
open MeasureTheory

namespace FreedmanTail.LowerTail

/-- Freedman (1975), (4.16:5), p. 110: `η₅ < P{W < b} · exp[(−½ + 2δ²)k]`. -/
theorem ineq_4_16_5
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Ω → ℝ) (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω) (δ a b : ℝ)
    (hU : LaplaceUpper P W a) (hL : LaplaceLower P W a) (hpar : ParamConditions δ a b) :
    eta P W δ a b (I5 δ b) <
      P.real {ω | W ω < b} * Real.exp ((-(1 / 2) + 2 * δ ^ 2) * kStar a b) := by sorry

end FreedmanTail.LowerTail
