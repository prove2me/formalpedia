-- Prove2me | Theorems.Thm_FreedmanTail_LowerTail_ineq_4_17
-- name    : FreedmanTail.LowerTail.ineq_4_17
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:11:49.497223+00:00
-- url     : https://prove2.me/theorems/e11d29c8-b964-4c84-bf40-68d7fabbab35
-- title:
--   (4.17) — exp(−δ²k/8) < 1/(8k) under (4.12)
-- statement:
--   Let $\delta,a,b$ be positive reals satisfying (4.12a)–(4.12c): $\delta<\tfrac13$, $b/a>9/\delta^2$ and $a^2/b>(16/\delta^2)\log(64/\delta^2)$. Put $k=a^2/b$. Then
--
--   $$
--   \exp\!\left(-\frac{\delta^2k}{8}\right)<\frac{1}{8k}.
--   $$
--
--   In the proof of Proposition (4.10) this is the fact that makes each of the error terms $\eta_2,\eta_3$ smaller than $\tfrac18\exp[-(1+\delta)k]$. It is the case $\alpha=64/\delta^2$, $x=\delta^2k/8$ of Lemma (4.9).
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 110 (PDF p. 11), display (4.17)

import Mathlib
import Definitions.Def_FreedmanTail_LowerTail_Exponents
import Definitions.Def_FreedmanTail_LowerTail_Hypotheses
import Definitions.Def_FreedmanTail_LowerTail_ProofNotation
open MeasureTheory

namespace FreedmanTail.LowerTail

/-- Freedman (1975), (4.17), p. 110: under (4.12), with `k = a²/b`,
`exp(−δ²k/8) < 1/(8k)`. -/
theorem ineq_4_17 (δ a b : ℝ) (hpar : ParamConditions δ a b) :
    Real.exp (-(δ ^ 2 * kStar a b / 8)) < 1 / (8 * kStar a b) := by sorry

end FreedmanTail.LowerTail
