-- Prove2me | Theorems.Thm_NewtonLCP_Supplement_theorem_7_6
-- name    : NewtonLCP.Supplement.theorem_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:20:31.89906+00:00
-- url     : https://prove2.me/theorems/51698723-eb90-45c6-ae91-8c74ee7150e0
-- title:
--   Theorem 7.6 — closed Rump theorem $\rho^S_0(M)\le1\iff C(M)\in P_0$
-- statement:
--   Let $M\in\mathbb R^{n\times n}$ be such that $I_n-M$ is nonsingular, and let $C(M)=(I_n-M)^{-1}(I_n+M)$ be its Cayley transform. Then
--
--   $$\rho^S_0(M)\le1\iff C(M)\in P_0,$$
--
--   where $\rho^S_0(M)=\max_{S}\rho(SM)$ is the sign-real spectral radius (the maximum over signature matrices $S=\mathrm{diag}(\pm1)$ of the largest absolute value of a real eigenvalue of $SM$, and $0$ if there is none), and $P_0$ is the class of matrices whose principal minors are all nonnegative.
--
--   This extends Rump's characterization of P-matrices ($\rho^S_0(M)<1\iff C(M)\in P$) to the closure $P_0$, and is the step of the proof of Theorem 1.3 that excludes the reduced matrix from $P_0$.
--
--   **Formalization Note** $\rho^S_0$ is the published `signRealSpecRad`, $P_0$ the published `IsP0`; nonsingularity is $\det(I_n-M)\neq0$.
--
--   Differences from the source: none.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Theorem 7.6, p.25 (restated and proved p.36)

import Mathlib
import Definitions.Def_NewtonLCP_Rump
import Definitions.Def_NewtonLCP_MatrixClasses
import Definitions.Def_NewtonLCP_Supplement_Cayley

namespace NewtonLCP.Supplement

/-- **Theorem 7.6** (closed Rump's theorem). Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Theorem 7.6, p.25 (restated and proved p.36).

For `M ∈ ℝⁿˣⁿ` such that `Iₙ − M` is nonsingular, `ρ^S_0(M) ≤ 1` if and only if `C(M) ∈ P₀`.

**Formalization Note.** `ρ^S_0` is the published `signRealSpecRad` (Definition 2.7 = 7.1, value
`0` when no `SM` has a real eigenvalue), `P₀` the published `IsP0`, and
`C(M) = (Iₙ − M)⁻¹(Iₙ + M)` is `cayley M`. Every `n ≥ 0`. -/
theorem theorem_7_6 {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ)
    (hM : (1 - M).det ≠ 0) :
    signRealSpecRad M ≤ 1 ↔ IsP0 (cayley M) := by sorry

end NewtonLCP.Supplement
