-- Prove2me | Theorems.Thm_LogSobolevMC_Metropolis_theorem_1_1
-- name    : LogSobolevMC.Metropolis.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:58:31.52063+00:00
-- url     : https://prove2.me/theorems/9b1b6138-8d24-45bd-85eb-f14d51127c8f
-- title:
--   Theorem 1.1, p. 698 — the Metropolis chain for the binomial distribution satisfies ‖M_xˡ − π‖_TV ≤ e^{1−c} for l ≥ (n/2)(log n + 2c)
-- statement:
--   Fix $n\ge 1$ and let $\pi(x)=2^{-n}\binom nx$ be the binomial distribution on $\{0,1,\dots,n\}$. Let $M$ be the Metropolis chain (1.9): starting from $x$, propose $x\pm1$ with probability $1/2$ each (a proposal outside $\{0,\dots,n\}$ is a hold), and accept a proposed move to $y$ with probability $\min\{1,\pi(y)/\pi(x)\}$, otherwise stay. Write $M^l_x=M^l(x,\cdot)$ for the law of the chain after $l$ steps from $x$ and $\|\mu-\nu\|_{TV}=\max_{A\subseteq\mathcal X}|\mu(A)-\nu(A)|$. Then for every $x$, every $c>0$ and every integer $l$,
--
--   $$\|M^l_x-\pi\|_{TV}\le e^{1-c}\qquad\text{for } l\ge\frac n2(\log n+2c).$$
--
--   So the Metropolis algorithm for the binomial distribution is close to stationarity after $\frac n2\log n+O(n)$ steps, while the spectral gap $\lambda(M)\asymp 1/n$ alone only gives order $n^2$.
--
--   **Formalization Note** This is the first (upper bound) statement of Theorem 1.1. The converse, $\max_x\|M^l_x-\pi\|_{TV}\ge 1/4+o(1)$ for $l\le (n/8)\log n$, is asymptotic, proved in the paper only by citation, and not part of this statement. The paper's derivation (Example 3.4) reaches $l\ge\frac n2(\log n+2c)+1$ in chi-square distance; the goal is the statement as printed, without the $+1$.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 698, Theorem 1.1 (first statement)

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_LogSobolevMC_Metropolis_Chains

namespace LogSobolevMC.Metropolis

/-- Theorem 1.1, p. 698 (upper bound): the Metropolis chain `M` of (1.9) for the binomial
distribution `π(x) = 2⁻ⁿ C(n, x)` on `{0, …, n}` satisfies
`‖M_xˡ − π‖_TV ≤ e^{1−c}` for every starting state `x`, every `c > 0` and every
`l ≥ (n/2)(log n + 2c)`. -/
theorem theorem_1_1 (n : ℕ) (hn : 1 ≤ n) (c : ℝ) (hc : 0 < c) (x : Fin (n + 1)) (l : ℕ)
    (hl : (n : ℝ) / 2 * (Real.log n + 2 * c) ≤ (l : ℝ)) :
    MarkovMixing.tvDist (MarkovMixing.rowDist (binomMetropolis n) l x) (binomPi n) ≤
      Real.exp (1 - c) := by sorry

end LogSobolevMC.Metropolis
