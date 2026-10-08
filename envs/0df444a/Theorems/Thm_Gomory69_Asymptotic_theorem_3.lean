-- Prove2me | Theorems.Thm_Gomory69_Asymptotic_theorem_3
-- name    : Gomory69.Asymptotic.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:02:57.505987+00:00
-- url     : https://prove2.me/theorems/5e0aa84d-766c-4ad1-b47e-191ddbd6eba5
-- title:
--   THEOREM 3, p. 461 — a minimizing vertex gives an optimal integer solution when B⁻¹(b − Nx_N*) ≥ 0
-- statement:
--   Consider the integer program (2), $\max c\cdot x$ subject to $Ax=b$, $x\ge0$ integer, with $A=(B,N)$ containing an $m\times m$ unit matrix, $B$ nonsingular and an optimal basis of the linear programming relaxation ($B^{-1}b\ge0$ and all relative prices $c^*_{m+i}\ge0$). Let $\mathcal G=M(I)/M(B)$, $\mathcal N$ the set of nonzero $fN_i$ and $g_0=fb$. Let $t^*$ be a vertex of $P(\mathcal G,\mathcal N,g_0)$ minimizing (8),
--
--   $$\min\ \sum_{g\in\mathcal N}c^*(g)t(g)\quad\text{subject to}\quad\sum_{g\in\mathcal N}g\cdot t(g)=g_0,\ t(g)\ge0\ \text{integer},$$
--
--   and let $x_N^*$ be the nonbasic part of a corresponding vertex of $P_x(B,N,b)$ with $Fx^*=t^*$ and $x_{m+i}>0$ only if $c^*_{m+i}=c^*(fN_i)$. If $B^{-1}(b-Nx_N^*)\ge0$, then $x_B^*=B^{-1}(b-Nx_N^*)$ is an integer vector and
--
--   $$x^*=\bigl(B^{-1}(b-Nx_N^*),\,x_N^*\bigr)$$
--
--   is an optimal solution of the integer program (2).
--
--   The theorem reduces the integer program to the group minimization problem whenever the basic part it produces is nonnegative.
--
--   **Formalization Note** "Corresponding vertex" is Remark 1 (p. 458) with the least-cost condition, as in the definition file. The optimal LP basis hypothesis is the standing assumption of pp. 460–461. Integrality of $x_B^*$ is part of the conclusion (the paper derives it from (3), p. 456).
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), p. 461, THEOREM 3

import Mathlib
import Definitions.Def_Gomory69_Asymptotic_GroupPolyhedron
import Definitions.Def_Gomory69_Asymptotic_IntegerProgram

namespace Gomory69.Asymptotic

/-- THEOREM 3 (p. 461): let `B` be an optimal linear programming basis of (2), `t*` a vertex
of `P(𝒢, 𝒩, f b)` minimizing (8), and `x_N*` the nonbasic part of a corresponding vertex
using only least cost columns. If `B⁻¹(b − N x_N*) ≥ 0`, then `x_B* = B⁻¹(b − N x_N*)` is an
integer vector and `x* = (x_B*, x_N*)` is an optimal solution of the integer program (2). -/
theorem theorem_3 {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (b : Fin m → ℤ) (c : Fin m ⊕ Fin n → ℝ)
    (hunit : ContainsUnitMatrix B N) (hdet : B.det ≠ 0) (hopt : IsOptimalLPBasis B N b c)
    (tstar : ↥(groupColumnSet B N) → ℝ) (ht : IsMinimizingVertex B N b c tstar)
    (xN : Fin n → ℕ) (hx : IsCorrespondingVertex B N c tstar xN)
    (hnonneg : ∀ k, 0 ≤ basicPart B N b xN k) :
    ∃ xB : Fin m → ℤ, (∀ k, (xB k : ℝ) = basicPart B N b xN k) ∧
      IsOptimal B N b c (Sum.elim xB (fun i => (xN i : ℤ))) := by sorry

end Gomory69.Asymptotic
