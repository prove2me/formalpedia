-- Prove2me | Theorems.Thm_LogSobolevMC_Metropolis_example_3_3_ehrenfest
-- name    : LogSobolevMC.Metropolis.example_3_3_ehrenfest
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:59:02.161396+00:00
-- url     : https://prove2.me/theorems/e4ea7331-723b-41f8-a509-27419e435ffd
-- title:
--   Example 3.3, pp. 718–719 — the Ehrenfest chain: projection of the hypercube walk, binomial stationary law, λ = 2/n, α(P) = 1/n
-- statement:
--   Fix $n\ge 1$. The hypercube walk $K$ of Example 3.2 induces, through the number of coordinates equal to $1$, the birth and death chain on $\{0,\dots,n\}$ with kernel
--
--   $$P(x,y)=\begin{cases}(n-x)/n, & y=x+1,\ 0\le x\le n-1,\\ x/n, & y=x-1,\ 1\le x\le n,\end{cases}$$
--
--   (the classical **Ehrenfest chain**): for every $x\in\{-1,1\}^n$ and every $k$, the probability that one step of $K$ from $x$ lands on a point with $k$ ones is $P(\#x,k)$, where $\#x$ is the number of ones of $x$. Its stationary measure is $\pi(x)=2^{-n}\binom nx$, its spectral gap is $\lambda=2/n$, and its log-Sobolev constant is
--
--   $$\alpha(P)=\frac1n.$$
--
--   The Ehrenfest chain is the comparison chain for the Metropolis chain of (1.9), which has the same stationary distribution.
--
--   **Formalization Note** The equality $\lambda=2/n$ is quoted by the paper as known; it is part of the claim.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), pp. 718–719, Example 3.3

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_LogSobolevMC_Metropolis_Setting
import Definitions.Def_LogSobolevMC_Metropolis_Chains

namespace LogSobolevMC.Metropolis

/-- Example 3.3, pp. 718–719 (first part): the hypercube chain of Example 3.2 induces, through
the number of coordinates equal to `1`, the Ehrenfest chain `P` on `{0, …, n}`, whose
stationary measure is the binomial `π(x) = 2⁻ⁿ C(n, x)`; its spectral gap is `λ = 2/n` and
its log-Sobolev constant is `α(P) = 1/n`. -/
theorem example_3_3_ehrenfest (n : ℕ) (hn : 1 ≤ n) :
    (∀ (x : Fin n → Fin 2) (k : Fin (n + 1)),
      ∑ y ∈ Finset.univ.filter (fun y => ones n y = k), hypercube n x y =
        ehrenfest n (ones n x) k) ∧
    MarkovMixing.IsStationary (ehrenfest n) (binomPi n) ∧
    LogSobolevMC.ChiSquare.gap (ehrenfest n) (binomPi n) = 2 / (n : ℝ) ∧
    LogSobolevMC.ChiSquare.logSobolev (ehrenfest n) (binomPi n) = 1 / (n : ℝ) := by sorry

end LogSobolevMC.Metropolis
