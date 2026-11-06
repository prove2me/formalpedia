-- Prove2me | Theorems.Thm_MatrixLewis_fact_3_6
-- name    : MatrixLewis.fact_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:06:29.126975+00:00
-- url     : https://prove2.me/theorems/706796ac-2a66-46dd-9553-e7b9c37bfceb
-- title:
--   Fact 3.6 — matrix Young inequality with equality case
-- statement:
--   Let $p>1$ and $p'=p/(p-1)$. For positive semidefinite $A,Z\in\mathbb S^n$,
--   $$
--   \frac1p\operatorname{tr}Z^p+\frac1{p'}\operatorname{tr}A^{p'}-\operatorname{tr}(AZ)\ \ge\ 0,
--   $$
--   with equality if and only if $A=Z^{p-1}$.
--
--   Its equality case identifies the maximizer of the matrix Lewis potential and gives the dual objective $F_{\mathrm{du}}$.
--
--   Differences from the source: none.
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Fact 3.6, p.18, eq. (6)

import Mathlib
import Definitions.Def_MatrixLewis_mpow

namespace MatrixLewis

/-- **Fact 3.6** (Matrix Young inequality; Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), p.18, eq. (6)). Let `p > 1` and
`p′ = p/(p − 1)`. For positive semidefinite `A, Z ∈ Sⁿ`,
`(1/p) tr Z^p + (1/p′) tr A^{p′} − tr(AZ) ≥ 0`, with equality if and only if `A = Z^{p−1}`.

**Formalization Note** Matrix powers are `mpow` (functional calculus with `Real.rpow`); `p′` is
local to the fact. -/
theorem fact_3_6 {n : ℕ} (p : ℝ) (hp : 1 < p) (A Z : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (hZ : Z.PosSemidef) :
    let p' := p / (p - 1)
    0 ≤ (1 / p) * (mpow p Z).trace + (1 / p') * (mpow p' A).trace - (A * Z).trace ∧
      ((1 / p) * (mpow p Z).trace + (1 / p') * (mpow p' A).trace - (A * Z).trace = 0 ↔
        A = mpow (p - 1) Z) := by sorry

end MatrixLewis
