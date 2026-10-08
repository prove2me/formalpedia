-- Prove2me | Theorems.Thm_LogSobolevMC_TwoPoint_theorem_A_1
-- name    : LogSobolevMC.TwoPoint.theorem_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:57:58.437699+00:00
-- url     : https://prove2.me/theorems/cc5fb154-7243-40f7-8c71-0a9b4feb6c5e
-- title:
--   Theorem A.1, pp. 742–743 — the chain K(x, y) = π(y) has α = (1 − 2π_*)/log(1/π_* − 1)
-- statement:
--   Let $\pi$ be a probability measure on a finite set $\mathcal X$ with $\pi(x)>0$ for every $x$, and set $\pi_*=\min_{\mathcal X}\pi$. Consider the Markov chain $K(x,y)=\pi(y)$, which has invariant measure $\pi$. If $\pi_*<1/2$, its log-Sobolev constant $\alpha$ is
--
--   $$\alpha=\frac{1-2\pi_*}{\log(1/\pi_*-1)}.$$
--
--   In particular, for the uniform measure $\pi\equiv1/|\mathcal X|$ on a set with $|\mathcal X|\ge3$ points,
--
--   $$\alpha=\frac{1-2/|\mathcal X|}{\log(|\mathcal X|-1)}.$$
--
--   This is the exact log-Sobolev constant of the simplest nontrivial chain, the one that forgets its state in one step. Since its spectral gap is $1$, it shows that $\alpha$ can be of smaller order than $\lambda/2$ (by a factor $\log(1/\pi_*)$) and gives the comparison bound of Corollary A.4 for every finite chain.
--
--   **Formalization Note** The page assumes only that $\pi$ is positive. The hypothesis $\pi_*<1/2$ (and $|\mathcal X|\ge3$ in the uniform case) is added and disclosed: $\pi_*\le1/2$ always holds when $|\mathcal X|\ge2$, and at $\pi_*=1/2$ (the uniform measure on two points) the printed formula is $0/0$, which Lean would evaluate to $0$, while the true value is $1/2$ (Theorem A.2 at $\theta=1/2$); on a one-point set $\pi_*=1$ and the formula is meaningless. The infimum (A.2) is Lean's `sInf` of the set of ratios.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), pp. 742–743, Theorem A.1

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_lower
import Definitions.Def_LogSobolevMC_TwoPoint_Setting

namespace LogSobolevMC.TwoPoint

open MarkovMixing

/-- Theorem A.1 (pp. 742–743): for a positive probability `π` on a finite set with
`π_* = min π < 1/2`, the chain `K(x, y) = π(y)` has invariant measure `π` and log-Sobolev constant
`(1 − 2π_*)/log(1/π_* − 1)`; in particular, for the uniform `π ≡ 1/|𝒳|` with `|𝒳| ≥ 3`,
`α = (1 − 2/|𝒳|)/log(|𝒳| − 1)`. -/
theorem theorem_A_1 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (π : V → ℝ) (hπ : IsDist π) (hπpos : ∀ x, 0 < π x) (hhalf : piMin π < 1 / 2) :
    IsStationary (indepChain π) π ∧
    LogSobolevMC.ChiSquare.logSobolev (indepChain π) π = (1 - 2 * piMin π) / Real.log (1 / piMin π - 1) ∧
      (3 ≤ Fintype.card V →
        LogSobolevMC.ChiSquare.logSobolev (indepChain (uniformDist V)) (uniformDist V) =
          (1 - 2 / (Fintype.card V : ℝ)) / Real.log ((Fintype.card V : ℝ) - 1)) := by sorry

end LogSobolevMC.TwoPoint
