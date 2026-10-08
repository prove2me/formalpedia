-- Prove2me | Theorems.Thm_LogSobolevMC_TwoPoint_corollary_A_3
-- name    : LogSobolevMC.TwoPoint.corollary_A_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:57:53.648996+00:00
-- url     : https://prove2.me/theorems/a83a8bdb-774b-4058-95ed-05da43382de2
-- title:
--   Corollary A.3, p. 746 — every two-point chain has α = K(0, 1)[1 − 2π(0)]/(π(1) log[π(1)/π(0)])
-- statement:
--   Let $K$ be a Markov kernel on $\mathcal X=\{0,1\}$ with stationary distribution $\pi$, positive at both points. If $\pi(0)<\pi(1)$, its log-Sobolev constant is
--
--   $$\alpha(K)=\frac{K(0,1)\,[1-2\pi(0)]}{\pi(1)\log[\pi(1)/\pi(0)]},$$
--
--   and if $\pi(1)<\pi(0)$ the same holds with the roles of $0$ and $1$ reversed.
--
--   This determines the log-Sobolev constant of every chain on a two-point space.
--
--   **Formalization Note** The page assumes $\pi(0)\le\pi(1)$. At $\pi(0)=\pi(1)=1/2$ the printed formula is $0/0$ (Lean's value $0$), so that case is excluded and disclosed: the statement assumes the strict inequality in each direction.
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), p. 746, Corollary A.3

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_lower
import Definitions.Def_LogSobolevMC_TwoPoint_Setting

namespace LogSobolevMC.TwoPoint

open MarkovMixing

/-- Corollary A.3 (p. 746): every Markov kernel on `{0, 1}` with positive stationary distribution
`π`, `π(0) < π(1)`, has `α = K(0, 1)[1 − 2π(0)]/(π(1) log[π(1)/π(0)])`; if `π(1) < π(0)`, the roles
of `0` and `1` are reversed. -/
theorem corollary_A_3 (K : Matrix (Fin 2) (Fin 2) ℝ) (hK : IsStochastic K) (π : Fin 2 → ℝ)
    (hπ : IsStationary K π) (hπpos : ∀ x, 0 < π x) :
    (π 0 < π 1 →
      LogSobolevMC.ChiSquare.logSobolev K π = K 0 1 * (1 - 2 * π 0) / (π 1 * Real.log (π 1 / π 0))) ∧
    (π 1 < π 0 →
      LogSobolevMC.ChiSquare.logSobolev K π = K 1 0 * (1 - 2 * π 1) / (π 0 * Real.log (π 0 / π 1))) := by sorry

end LogSobolevMC.TwoPoint
