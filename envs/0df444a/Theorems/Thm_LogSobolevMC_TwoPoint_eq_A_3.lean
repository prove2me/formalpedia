-- Prove2me | Theorems.Thm_LogSobolevMC_TwoPoint_eq_A_3
-- name    : LogSobolevMC.TwoPoint.eq_A_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:58:04.537246+00:00
-- url     : https://prove2.me/theorems/b1af2b28-36eb-467f-85fa-8e827315f3a9
-- title:
--   (A.3), p. 747 — a minimizer u of (A.2) solves 2u log u − 2u log‖u‖₂ − (1/α)(I − K)u = 0
-- statement:
--   Let $K$ be a Markov kernel on a finite set $\mathcal X$, reversible with respect to its invariant probability $\pi>0$ (that is, $\pi(x)K(x,y)=\pi(y)K(y,x)$), and suppose its log-Sobolev constant $\alpha$ is positive. Let $u$ be a positive function with $\mathcal L(u)\neq0$ that attains the infimum (A.2), $\mathcal E(u,u)=\alpha\mathcal L(u)$. Then at every point of $\mathcal X$
--
--   $$2u\log u-2u\log\|u\|_2-\frac1\alpha(I-K)u=0. \tag{A.3}$$
--
--   This Euler–Lagrange equation is what makes a minimizer for $K(x,y)=\pi(y)$ take at most two values, reducing Theorem A.1 to the two-point Theorem A.2.
--
--   **Formalization Note** The page says "any minimizer u of (A.2)" in a context where minimizers are nonnegative. Three hypotheses are added and disclosed: reversibility (for a nonreversible kernel the variational equation involves the symmetric part $\tfrac12(K+K^*)$ rather than $K$; the page applies (A.3) only to the reversible chain $K(x,y)=\pi(y)$); positivity of $u$ (the logarithm at a zero of $u$ would take Lean's default value); and $\alpha>0$ (so that $1/\alpha$ is meaningful).
-- source:
--   Diaconis and Saloff-Coste, Logarithmic Sobolev inequalities for finite Markov chains, Ann. Appl. Probab. 6 (1996), pp. 746–747, proof of Theorem A.1, (A.3)

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_lower
import Definitions.Def_LogSobolevMC_TwoPoint_Setting

namespace LogSobolevMC.TwoPoint

open MarkovMixing

/-- (A.3), p. 747: a positive minimizer `u` of (A.2) for a reversible chain satisfies
`2u log u − 2u log ‖u‖₂ − (1/α)(I − K)u = 0`. -/
theorem eq_A_3 {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : IsStochastic K) (π : V → ℝ) (hπ : IsStationary K π)
    (hπpos : ∀ x, 0 < π x) (hrev : DetailedBalance K π)
    (u : V → ℝ) (hu : ∀ x, 0 < u x) (hne : LogSobolevMC.ChiSquare.entL π u ≠ 0)
    (hmin : LogSobolevMC.ChiSquare.dirichlet K π u u = LogSobolevMC.ChiSquare.logSobolev K π * LogSobolevMC.ChiSquare.entL π u)
    (hα : 0 < LogSobolevMC.ChiSquare.logSobolev K π) :
    ∀ x, 2 * u x * Real.log (u x) - 2 * u x * Real.log (LogSobolevMC.ChiSquare.lpNorm π 2 u)
      - (1 / LogSobolevMC.ChiSquare.logSobolev K π) * (u x - K.mulVec u x) = 0 := by sorry

end LogSobolevMC.TwoPoint
