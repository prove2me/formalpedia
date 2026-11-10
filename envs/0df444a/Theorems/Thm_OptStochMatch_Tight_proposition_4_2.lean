-- Prove2me | Theorems.Thm_OptStochMatch_Tight_proposition_4_2
-- name    : OptStochMatch.Tight.proposition_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:55:24.79471+00:00
-- url     : https://prove2.me/theorems/acd62680-a2c5-46a4-9e16-bfaf47f10487
-- title:
--   Proposition 4.2 — closed form of the comparison policy's continuation value
-- statement:
--   For $0\le t\le1$ and $h\ge0$, $q(t,h)=1-\exp\!\big(-(h+1)(e^{1-t}-1)\big)$ (4.4). In particular $q(1,h)=0$ and $q(0,0)=1-e^{1-e}$.
--
--   Differences from the source:
--   - encoding: q(t, h), the expected additional work by time 1 under the comparison policy → E[min(E, ψ(1) − h)], E ∼ Exp(1), ψ the solution of ψ' = ψ + 1, ψ(t) = h; reason: the comparison policy serves at rate x' = x + 1 until completion or the deadline, with a unit-exponential residual demand
-- source:
--   Dütting, Feldman, Molina, Optimal Online Stochastic Matching, arXiv:2610.19866 (sha256 0458ce2e…), Proposition 4.2, eq. (4.4), p. 15 (PDF p. 16)

import Mathlib
import Definitions.Def_OptStochMatch_Tight_Comparison

namespace OptStochMatch.Tight

/-- Proposition 4.2 (p. 15, PDF 16). For `0 ≤ t ≤ 1` and `h ≥ 0`, the continuation value of the
comparison policy is `q(t, h) = 1 − exp(−(h + 1)(e^{1−t} − 1))` (4.4). In particular
`q(1, h) = 0` and `q(0, 0) = 1 − e^{1−e}`. -/
theorem proposition_4_2 :
    (∀ t h : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ h →
      qComp t h = 1 - Real.exp (-((h + 1) * (Real.exp (1 - t) - 1)))) ∧
    (∀ h : ℝ, 0 ≤ h → qComp 1 h = 0) ∧
    qComp 0 0 = 1 - Real.exp (1 - Real.exp 1) := by sorry

end OptStochMatch.Tight
