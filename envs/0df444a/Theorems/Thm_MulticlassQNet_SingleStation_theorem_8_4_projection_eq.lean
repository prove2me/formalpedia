-- Prove2me | Theorems.Thm_MulticlassQNet_SingleStation_theorem_8_4_projection_eq
-- name    : MulticlassQNet.SingleStation.theorem_8_4_projection_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:13:32.875521+00:00
-- url     : https://prove2.me/theorems/fa2756ed-e919-4c77-904f-9f2c02971f8f
-- title:
--   Theorem 8.4 — the O(n²)-variable polyhedron P2 projects exactly onto the M/M/1 performance polymatroid P1
-- statement:
--   Consider a single-server queue with classes $E=\{1,\dots,n\}$, arrival rates $\lambda_i>0$, service rates $\mu_i>0$, traffic intensities $\rho_i=\lambda_i/\mu_i$ and load $\sum_{i\in E}\rho_i<1$. Let P1 be the polyhedron of $(n_i)\in\mathbb R_+^n$ with
--   $$
--   \sum_{i\in S}\frac{n_i}{\mu_i}\ \ge\ \frac{\sum_{i\in S}\rho_i/\mu_i}{1-\sum_{i\in S}\rho_i}\quad(S\subset E),\qquad \sum_{i\in E}\frac{n_i}{\mu_i}=\frac{\sum_{i\in E}\rho_i/\mu_i}{1-\sum_{i\in E}\rho_i},
--   $$
--   and let P2 be the polyhedron of nonnegative $(n_i)_{i\in E}$, $(I_{ij})_{i,j\in E}$ with
--   $$
--   \begin{aligned}
--   \mu_iI_{ii}-\lambda_in_i&=\lambda_i, && i\in E,\\
--   \mu_iI_{ij}+\mu_jI_{ji}-\lambda_jn_i-\lambda_in_j&=0, && i,j\in E,\ i\neq j,\\
--   \textstyle\sum_{i\in E}I_{ij}&=n_j, && j\in E.
--   \end{aligned}
--   $$
--   Then the projection of P2 onto the $n_i$ coordinates is exactly P1:
--   $$
--   \{(n_i)_{i\in E}:\ \exists\,(I_{ij})\ \text{with}\ ((n_i),(I_{ij}))\in\mathrm{P2}\}=\mathrm{P1}.
--   $$
--
--   P1 is described by $2^n-1$ constraints in $n$ variables; P2 by $O(n^2)$ constraints in $O(n^2)$ variables. The theorem therefore gives a polynomial-size extended formulation of the performance polymatroid of the multiclass M/M/1 queue under preemptive work-conserving scheduling.
--
--   **Formalization Note** Both inclusions are asserted. The statement is purely polyhedral: the paper's derivation of P2 from the queue (via Theorem 4.2) and of P1 as the achievable region (Theorem 8.3) involve policies and invariant distributions that do not appear here. The paper writes $N$ for the class set $E$ in (65) and (71). Conventions are those of the definition `MulticlassQNet.SingleStation.Polyhedra`.
-- source:
--   Bertsimas, Paschalidis, Tsitsiklis, Optimization of Multiclass Queueing Networks: Polyhedral and Nonlinear Characterizations of Achievable Performance, MIT Sloan WP #3509-92-MSA (Dec. 1992), p. 38, Theorem 8.4, Eqs. (69)–(71); P1 from Theorem 8.3, pp. 35–36, Eqs. (64)–(65)

import Mathlib
import Definitions.Def_MulticlassQNet_SingleStation_Polyhedra

namespace MulticlassQNet.SingleStation

/-- Theorem 8.4 (p. 38): the polyhedron P2, defined by (69)–(71) and nonnegativity in the
`O(n²)` variables `(n_i, I_ij)`, projected on the `n_i` coordinates, is exactly P1. -/
theorem theorem_8_4_projection_eq {n : ℕ} (lam mu : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hmu : ∀ i, 0 < mu i) (hload : ∑ i, lam i / mu i < 1) :
    {x : Fin n → ℝ | ∃ I, (x, I) ∈ P2 lam mu} = P1 lam mu := by sorry

end MulticlassQNet.SingleStation
