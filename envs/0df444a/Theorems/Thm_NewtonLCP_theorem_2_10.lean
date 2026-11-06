-- Prove2me | Theorems.Thm_NewtonLCP_theorem_2_10
-- name    : NewtonLCP.theorem_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:28:45.295503+00:00
-- url     : https://prove2.me/theorems/2dfa07b2-a9c1-401c-af28-ebb93ba8e8ee
-- title:
--   Theorem 2.10 — Rump's bounds $\zeta(M)/(3+2\sqrt2)\le\rho^S_0(M)\le n\,\zeta(M)$
-- statement:
--   For every $M\in\mathbb R^{n\times n}$, the sign-real spectral radius and the maximum absolute geometric cycle mean satisfy
--
--   $$\frac{\zeta(M)}{3+2\sqrt2}\ \le\ \rho^S_0(M)\ \le\ n\cdot\zeta(M).$$
--
--   This is Rump's theorem [Rum97, Theorem 5.5], cited in the paper. The lower bound turns the spectral bound $\rho^S_0((I_n+A)^{-1})\le1$ for $A\in P_0$ into a bound on cycle products, from which the Rump weights are built.
--
--   Differences from the source: none.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), Theorem 2.10, p.7 (cited)

import Mathlib
import Definitions.Def_NewtonLCP_Rump

namespace NewtonLCP

/-- **Theorem 2.10** (Rump [Rum97, Theorem 5.5]). Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Theorem 2.10, p.7 (cited; not proved in
the paper).

For any `M ∈ ℝⁿˣⁿ`, `ζ(M)/(3 + 2√2) ≤ ρ^S_0(M) ≤ n · ζ(M)`.

**Formalization Note.** `n = Fintype.card ι`; `ρ^S_0` and `ζ` as in Definitions 2.7 and 2.9 (see
`NewtonLCP.Rump`). Both inequalities are stated. -/
theorem theorem_2_10 {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) :
    cycleMean M / (3 + 2 * Real.sqrt 2) ≤ signRealSpecRad M ∧
      signRealSpecRad M ≤ (Fintype.card ι : ℝ) * cycleMean M := by sorry

end NewtonLCP
