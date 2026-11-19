-- Prove2me | Theorems.Thm_MersenneLPW_lenstra_pomerance_wagstaff
-- name    : MersenneLPW.lenstra_pomerance_wagstaff
-- status  : Open
-- author  : @LG
-- created : 2026-11-18T15:26:46.208937+00:00
-- url     : https://prove2.me/theorems/cfb9539f-5365-495b-8f15-8bc04e7c206d
-- title:
--   Lenstra–Pomerance–Wagstaff conjecture
-- statement:
--   The **Lenstra–Pomerance–Wagstaff (LPW) conjecture**: the number of exponents $p < y$ for which $2^p - 1$ is a Mersenne prime is asymptotic to $e^{\gamma}\log_2 y$ as $y \to \infty$, where $\gamma$ is the Euler–Mascheroni constant:
--   $$C(y) \sim e^{\gamma}\,\log_2 y \;=\; \frac{e^{\gamma}}{\log 2}\,\log y.$$
--   Equivalently, the number of Mersenne primes below $x$ is asymptotic to $\frac{e^\gamma}{\log 2}\log\log x$. The conjecture predicts about $e^\gamma \approx 1.78$ Mersenne primes per doubling of the exponent bound, and about $e^\gamma \log_2 10 \approx 5.92$ per decimal digit of the exponent. It is open, and strictly stronger than the infinitude of Mersenne primes (the mission's goal). The heuristic originates with Gillies (1964) and Wagstaff (1983), as developed by Lenstra, Pomerance and Wagstaff.
--
--   **Formalization Note.** $C$ is `MersenneLPW.mersenneExponentCount`, built from `Nat.count` with the strict bound $p < y$ (the $<$ versus $\le$ convention is asymptotically immaterial). `Asymptotics.IsEquivalent Filter.atTop f g` means $f - g = o(g)$ along `atTop` on $\mathbb{N}$; values are real, `Real.logb 2 y = Real.log y / Real.log 2` with $y$ cast to $\mathbb{R}$ (its junk value at $y = 0$ is irrelevant along `atTop`), and $\gamma$ is `Real.eulerMascheroniConstant`. The constant is exact, not a numerical approximation. The statement follows the FormalConjectures formalization (PR #7866).
-- source:
--   S. S. Wagstaff Jr., Divisors of Mersenne numbers, Math. Comp. 40 (161) (1983), 385-397, doi:10.1090/S0025-5718-1983-0679454-X ; heuristic derivation: C. Caldwell, https://t5k.org/mersenne/heuristic.html ; https://en.wikipedia.org/wiki/Mersenne_conjectures#Lenstra%E2%80%93Pomerance%E2%80%93Wagstaff_conjecture ; Lean statement: FormalConjectures PR #7866, https://github.com/google-deepmind/formal-conjectures/pull/7866

import Mathlib
import Definitions.Def_MersenneLPW_mersenneExponentCount

namespace MersenneLPW

theorem lenstra_pomerance_wagstaff :
    Asymptotics.IsEquivalent Filter.atTop
      (fun y => (mersenneExponentCount y : ℝ))
      (fun y => Real.exp Real.eulerMascheroniConstant * Real.logb 2 y) := by sorry

end MersenneLPW
