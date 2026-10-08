-- Prove2me | Theorems.Thm_Gomory69_Asymptotic_theorem_4
-- name    : Gomory69.Asymptotic.theorem_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:03:39.506951+00:00
-- url     : https://prove2.me/theorems/2982135d-0a85-4152-85d6-3a84082d734a
-- title:
--   THEOREM 4, p. 462 — for b ∈ K_B(l_max(D − 1)) a minimizing vertex gives an optimal integer solution
-- statement:
--   Consider the integer program (2), $\max c\cdot x$ subject to $Ax=b$, $x\ge0$ integer, with $A=(B,N)$ an integer matrix containing an $m\times m$ unit matrix, $B$ nonsingular and an optimal basis of the linear programming relaxation (all relative prices $c^*_{m+i}\ge0$, $B^{-1}b\ge0$). Let $D=|\det B|$, $l_{\max}$ the Euclidean length of the longest nonbasic column, $\mathcal G=M(I)/M(B)$, $\mathcal N$ the set of nonzero $fN_i$, and suppose
--
--   $$b\in K_B\bigl(l_{\max}(D-1)\bigr).$$
--
--   Let $t^*$ be a vertex of $P(\mathcal G,\mathcal N,fb)$ minimizing (8), $\sum_{g\in\mathcal N}c^*(g)t(g)$ over the nonnegative integer solutions of $\sum_g t(g)\cdot g=fb$, and let $x_N^*$ be the nonbasic part of a corresponding vertex of $P_x(B,N,b)$ using only least cost columns. Then $x_B^*=B^{-1}(b-Nx_N^*)$ is a nonnegative integer vector and $x^*=(x_B^*,x_N^*)$ is an optimal integer solution of (2).
--
--   This is the asymptotic theorem of integer programming in its vertex form: for right-hand sides far enough inside the cone of an optimal LP basis, the integer program is solved by the group problem, and the answer can be read off a vertex of the corner polyhedron.
--
--   **Formalization Note** "The $x^*$ of Theorem 3" is spelled out: $t^*$ is an extreme point of $P(\mathcal G,\mathcal N,fb)$ that minimizes (8) over the integer solutions, and $x_N^*$ satisfies Remark 1 (i)–(iii) and the least-cost condition. $K_B(d)$ uses Euclidean distance to the frontier of $K_B$. The conclusion states that the basic part is integral, nonnegativity and feasibility being part of optimality.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 462, THEOREM 4

import Mathlib
import Definitions.Def_Gomory69_Asymptotic_GroupPolyhedron
import Definitions.Def_Gomory69_Asymptotic_IntegerProgram

namespace Gomory69.Asymptotic

/-- THEOREM 4 (p. 462): let `B` be an optimal linear programming basis of (2), `D = |det B|`,
`l_max` the Euclidean length of the longest nonbasic column, and `b ∈ K_B(l_max (D − 1))`.
If `t*` is a vertex of `P(𝒢, 𝒩, f b)` minimizing (8) and `x_N*` the nonbasic part of a
corresponding vertex using only least cost columns, then `x_B* = B⁻¹(b − N x_N*)` is an
integer vector and `x* = (x_B*, x_N*)` is an optimal solution of the integer program (2). -/
theorem theorem_4 {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (c : Fin m ⊕ Fin n → ℝ)
    (hunit : ContainsUnitMatrix B N) (hdet : B.det ≠ 0) (hopt : IsOptimalLPBasis B N b c)
    (hb : realVec b ∈ deepCone B (lmax N * ((detAbs B : ℝ) - 1)))
    (tstar : ↥(groupColumnSet B N) → ℝ) (ht : IsMinimizingVertex B N b c tstar)
    (xN : Fin n → ℕ) (hx : IsCorrespondingVertex B N c tstar xN) :
    ∃ xB : Fin m → ℤ, (∀ k, (xB k : ℝ) = basicPart B N b xN k) ∧
      IsOptimal B N b c (Sum.elim xB (fun i => (xN i : ℤ))) := by sorry

end Gomory69.Asymptotic
