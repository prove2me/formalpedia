-- Prove2me | Theorems.Thm_LogSobolevMC_Metropolis_example_3_3_metropolis
-- name    : LogSobolevMC.Metropolis.example_3_3_metropolis
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T20:00:32.135775+00:00
-- url     : https://prove2.me/theorems/7cfbcbc9-f34f-4d0a-8cfd-f7ab3b11bf1e
-- title:
--   Example 3.3, p. 719 — the Metropolis chain (1.9) has 1/n ≤ λ(M) ≤ 2/n and 1/(2n) ≤ α(M) ≤ 1/n
-- statement:
--   Fix $n\ge 1$, let $M$ be the Metropolis chain (1.9), $P$ the Ehrenfest chain and $\pi(x)=2^{-n}\binom nx$. Then $\pi$ is stationary for $M$,
--
--   $$\tfrac12\lambda(P)\le\lambda(M)\le\lambda(P),\qquad \tfrac12\alpha(P)\le\alpha(M)\le\alpha(P),$$
--
--   and hence
--
--   $$\frac1n\le\lambda(M)\le\frac2n,\qquad \frac1{2n}\le\alpha(M)\le\frac1n.$$
--
--   The lower bounds on $\lambda(M)$ and $\alpha(M)$ are the inputs of the convergence bound of Example 3.4 and Theorem 1.1.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 719, Example 3.3

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_LogSobolevMC_Metropolis_Setting
import Definitions.Def_LogSobolevMC_Metropolis_Chains

namespace LogSobolevMC.Metropolis

/-- Example 3.3, p. 719 (conclusion): the Metropolis chain `M` of (1.9) has the binomial
distribution as stationary measure, `½λ(P) ≤ λ(M) ≤ λ(P)` and `½α(P) ≤ α(M) ≤ α(P)` for the
Ehrenfest chain `P`, and hence `1/n ≤ λ(M) ≤ 2/n` and `1/(2n) ≤ α(M) ≤ 1/n`. -/
theorem example_3_3_metropolis (n : ℕ) (hn : 1 ≤ n) :
    MarkovMixing.IsStationary (binomMetropolis n) (binomPi n) ∧
    (1 / 2 * LogSobolevMC.ChiSquare.gap (ehrenfest n) (binomPi n) ≤ LogSobolevMC.ChiSquare.gap (binomMetropolis n) (binomPi n) ∧
      LogSobolevMC.ChiSquare.gap (binomMetropolis n) (binomPi n) ≤ LogSobolevMC.ChiSquare.gap (ehrenfest n) (binomPi n)) ∧
    (1 / 2 * LogSobolevMC.ChiSquare.logSobolev (ehrenfest n) (binomPi n) ≤ LogSobolevMC.ChiSquare.logSobolev (binomMetropolis n) (binomPi n) ∧
      LogSobolevMC.ChiSquare.logSobolev (binomMetropolis n) (binomPi n) ≤ LogSobolevMC.ChiSquare.logSobolev (ehrenfest n) (binomPi n)) ∧
    (1 / (n : ℝ) ≤ LogSobolevMC.ChiSquare.gap (binomMetropolis n) (binomPi n) ∧
      LogSobolevMC.ChiSquare.gap (binomMetropolis n) (binomPi n) ≤ 2 / (n : ℝ)) ∧
    (1 / (2 * (n : ℝ)) ≤ LogSobolevMC.ChiSquare.logSobolev (binomMetropolis n) (binomPi n) ∧
      LogSobolevMC.ChiSquare.logSobolev (binomMetropolis n) (binomPi n) ≤ 1 / (n : ℝ)) := by sorry

end LogSobolevMC.Metropolis
