-- Prove2me | Theorems.Thm_NewtonLCP_theorem_2_1
-- name    : NewtonLCP.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:28:43.121326+00:00
-- url     : https://prove2.me/theorems/d1617aac-21ce-4711-8c7f-0b6a67ac033b
-- title:
--   Theorem 2.1 — a row sufficient LCP is solvable iff it is feasible
-- statement:
--   Let $M\in\mathbb R^{n\times n}$ be row sufficient and $q\in\mathbb R^n$. Then LCP$(M,q)$ has a complementary solution if and only if
--
--   $$\mathcal F(M,q)\neq\emptyset .$$
--
--   Algorithm 3 uses this to reduce the solvability of LCP$(M,q)$ to the feasibility of a linear program (line 15). The result is cited in the paper (LCP duality, [FT92], [INT09], [CPS09, §3.5]).
--
--   Differences from the source: none.
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), Theorem 2.1, p.6 (cited)

import Mathlib
import Definitions.Def_NewtonLCP_LCP
import Definitions.Def_NewtonLCP_MatrixClasses

namespace NewtonLCP

/-- **Theorem 2.1** (solvability of row sufficient LCPs). Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Theorem 2.1, p.6 (cited from
[FT92], [INT09], [CPS09, §3.5]; not proved in the paper).

Let `M ∈ ℝⁿˣⁿ` be row sufficient and `q ∈ ℝⁿ`. Then LCP(M, q) has a complementary solution if
and only if `F(M, q) ≠ ∅`. -/
theorem theorem_2_1 {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (q : ι → ℝ)
    (hM : IsRowSufficient M) :
    (∃ x s, IsLCPSol M q x s) ↔ (Feas M q).Nonempty := by sorry

end NewtonLCP
