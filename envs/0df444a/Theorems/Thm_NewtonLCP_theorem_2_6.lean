-- Prove2me | Theorems.Thm_NewtonLCP_theorem_2_6
-- name    : NewtonLCP.theorem_2_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:28:42.17376+00:00
-- url     : https://prove2.me/theorems/40ba7d0b-6ad6-46dc-a454-68b479f58f9f
-- title:
--   Theorem 2.6 — $\hat\kappa(M)=\hat\kappa(M^\top)$ (Väliaho)
-- statement:
--   For every $M\in\mathcal P_\star\cap\mathbb R^{n\times n}$, the transpose $M^\top$ is also in $\mathcal P_\star$, and
--
--   $$\hat\kappa(M)=\hat\kappa(M^\top).$$
--
--   Together with the column sufficiency of $\mathcal P_\star$-matrices this makes every $\mathcal P_\star$-matrix row sufficient, which is what the solvability criterion (Theorem 2.1) needs.
--
--   Differences from the source: none.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), Theorem 2.6, p.7

import Mathlib
import Definitions.Def_NewtonLCP_Handicap

namespace NewtonLCP

/-- **Theorem 2.6** (Väliaho). Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Theorem 2.6, p.7 (proof from Theorem 1.1, p.7).

For any `M ∈ P⋆ ∩ ℝⁿˣⁿ`, `Mᵀ ∈ P⋆` and `κ̂(M) = κ̂(Mᵀ)`. -/
theorem theorem_2_6 {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (hM : IsPStar M) :
    IsPStar M.transpose ∧ handicap M = handicap M.transpose := by sorry

end NewtonLCP
