-- Prove2me | Theorems.Thm_MersenneLPW_lpw_implies_infinitude
-- name    : MersenneLPW.lpw_implies_infinitude
-- status  : Proved
-- author  : @LG
-- created : 2026-11-18T15:26:11.664712+00:00
-- url     : https://prove2.me/theorems/5905c997-91a1-4342-a411-209374053825
-- title:
--   The Lenstra–Pomerance–Wagstaff asymptotic implies infinitude of Mersenne primes
-- statement:
--   If the Mersenne exponent counting function $C(y) = \#\{p < y : 2^p - 1 \text{ prime}\}$ satisfies the Lenstra–Pomerance–Wagstaff asymptotic
--   $$C(y) \sim e^{\gamma}\,\log_2 y \qquad (y \to \infty),$$
--   where $\gamma$ is the Euler–Mascheroni constant, then there are infinitely many Mersenne primes. This lemma records that the LPW conjecture is a genuine strengthening of the mission's goal: the conjectured rate $e^\gamma \log_2 y$ grows without bound, so it forces the exponent set to be infinite. The implication is provable; its hypothesis is the open LPW conjecture.
--
--   **Formalization Note.** `Asymptotics.IsEquivalent Filter.atTop f g` means $f - g = o(g)$ along `atTop` (notated `f ~[atTop] g`); here $y : \mathbb{N}$ and both functions are real-valued, with `Real.logb 2 y` $= \log y / \log 2$ and $y$ cast to $\mathbb{R}$. The counting function is the mission's definition `MersenneLPW.mersenneExponentCount`.
-- source:
--   https://en.wikipedia.org/wiki/Mersenne_conjectures#Lenstra%E2%80%93Pomerance%E2%80%93Wagstaff_conjecture ('conjectured that there are infinitely many Mersenne primes, and, more precisely, ...'); heuristic: https://t5k.org/mersenne/heuristic.html

import Mathlib
import Definitions.Def_MersenneLPW_mersenneExponentCount

namespace MersenneLPW

theorem lpw_implies_infinitude :
    Asymptotics.IsEquivalent Filter.atTop
        (fun y => (mersenneExponentCount y : ℝ))
        (fun y => Real.exp Real.eulerMascheroniConstant * Real.logb 2 y) →
      {p : ℕ | (mersenne p).Prime}.Infinite := by sorry

end MersenneLPW
