-- Prove2me | Theorems.Thm_MatrixAnalytic_PH_nondefective_absorbing_representation
-- name    : MatrixAnalytic.PH.nondefective_absorbing_representation
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:40:50.615309+00:00
-- url     : https://prove2.me/theorems/05a32fdb-2489-4495-bcab-b2401c53b925
-- title:
--   Theorem 2.4.2 — a nondefective PH distribution has a representation absorbing a.s. from every phase
-- statement:
--   Let $(\boldsymbol\tau, T)$ be a continuous PH representation on a finite phase set, and suppose the distribution $\mathrm{PH}(\boldsymbol\tau, T)$ is **nondefective**: its distribution function satisfies $F(x) \to 1$ as $x \to \infty$. Then there exist $m \ge 0$ and a PH representation $(\boldsymbol\tau', T')$ with phases $\{1, \dots, m\}$ such that
--
--   1. starting from any phase $i \in \{1, \dots, m\}$, absorption into state $0$ occurs with probability 1 for the process with generator built from $T'$, and
--   2. $\mathrm{PH}(\boldsymbol\tau', T')$ and $\mathrm{PH}(\boldsymbol\tau, T)$ are the same distribution:
--   $$F_{(\boldsymbol\tau', T')}(x) = F_{(\boldsymbol\tau, T)}(x) \qquad \text{for all } x \ge 0.$$
--
--   The theorem justifies the standing convention, adopted on p. 44 of the book, that a nondefective PH distribution is always given by a representation with a nonsingular $T$.
--
--   **Formalization Note** "Absorption with probability 1 from phase $i$" is $\exp(Q'x)_{i0} \to 1$ as $x \to \infty$; distribution functions are the path-free `cdf` of `MatrixAnalytic.PH.Continuous`, compared on $[0, \infty)$, where they determine the distribution. The new phase set is `Fin m`; $m = 0$ is allowed (the empty representation is the point mass at $0$).
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 42, Theorem 2.4.2

import Mathlib
import Definitions.Def_MatrixAnalytic_PH_Continuous

open Matrix

namespace MatrixAnalytic.PH

/-- Theorem 2.4.2 (Latouche–Ramaswami, p. 42): every nondefective PH distribution has a
representation `(τ', T')` from every phase of which absorption into 0 occurs with probability 1.
"Same distribution" is equality of the distribution functions on `[0, ∞)`. -/
theorem nondefective_absorbing_representation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) (hrep : IsPHRep τ T) (hnd : Nondefective τ T) :
    ∃ (m : ℕ) (τ' : Fin m → ℝ) (T' : Matrix (Fin m) (Fin m) ℝ),
      IsPHRep τ' T' ∧ (∀ i, AbsorbedAS T' i) ∧ ∀ x : ℝ, 0 ≤ x → cdf τ' T' x = cdf τ T x := by sorry

end MatrixAnalytic.PH
