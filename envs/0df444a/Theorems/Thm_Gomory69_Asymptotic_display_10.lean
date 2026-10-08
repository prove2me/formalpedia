-- Prove2me | Theorems.Thm_Gomory69_Asymptotic_display_10
-- name    : Gomory69.Asymptotic.display_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:03:49.863632+00:00
-- url     : https://prove2.me/theorems/2a80bf50-6545-47e1-9d49-4d69ec0b66b0
-- title:
--   Display (10), p. 464 — the optimal x* of THEOREM 4 satisfies ∏(1 + x_{m+i}) ≤ D
-- statement:
--   Under the hypotheses of THEOREM 4 ($b\in K_B(l_{\max}(D-1))$, $B$ an optimal LP basis, $t^*$ a vertex of $P(\mathcal G,\mathcal N,fb)$ minimizing (8), $x_N^*$ a corresponding vertex using only least cost columns), the optimal integer solution $x^*=(B^{-1}(b-Nx_N^*),x_N^*)$ of (2) also satisfies
--
--   $$\prod_{i=1}^{n}\bigl(1+x^*_{m+i}\bigr)\le D,\qquad D=|\det B|.$$
--
--   So there are optimal integer programming solutions whose nonbasic part is small in this multiplicative sense.
--
--   **Formalization Note** The paper says "there are optimal integer programming solutions $x$ to (2) with" this bound; it is stated here for the specific optimal solution $x^*$ built from a minimizing vertex, which is the solution the paper's argument produces (the existence of a minimizing vertex is taken for granted on p. 461 and is not part of this statement).
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 464, display (10)

import Mathlib
import Definitions.Def_Gomory69_Asymptotic_GroupPolyhedron
import Definitions.Def_Gomory69_Asymptotic_IntegerProgram

namespace Gomory69.Asymptotic

/-- Display (10) (p. 464): under the hypotheses of THEOREM 4, the optimal solution
`x* = (B⁻¹(b − N x_N*), x_N*)` obtained from a minimizing vertex also satisfies
`∏_{i=1}^{n} (1 + x*_{m+i}) ≤ D`, `D = |det B|`. -/
theorem display_10 {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (c : Fin m ⊕ Fin n → ℝ)
    (hunit : ContainsUnitMatrix B N) (hdet : B.det ≠ 0) (hopt : IsOptimalLPBasis B N b c)
    (hb : realVec b ∈ deepCone B (lmax N * ((detAbs B : ℝ) - 1)))
    (tstar : ↥(groupColumnSet B N) → ℝ) (ht : IsMinimizingVertex B N b c tstar)
    (xN : Fin n → ℕ) (hx : IsCorrespondingVertex B N c tstar xN) :
    ∃ xB : Fin m → ℤ, (∀ k, (xB k : ℝ) = basicPart B N b xN k) ∧
      IsOptimal B N b c (Sum.elim xB (fun i => (xN i : ℤ))) ∧
      ∏ i : Fin n, (1 + xN i) ≤ detAbs B := by sorry

end Gomory69.Asymptotic
