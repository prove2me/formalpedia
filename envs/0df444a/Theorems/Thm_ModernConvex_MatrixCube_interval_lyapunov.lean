-- Prove2me | Theorems.Thm_ModernConvex_MatrixCube_interval_lyapunov
-- name    : ModernConvex.MatrixCube.interval_lyapunov
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:46.038984+00:00
-- url     : https://prove2.me/theorems/9fd3082c-1bc7-4699-b1e7-645416bccf00
-- title:
--   Proposition 4.4.6 — interval Lyapunov stability: ρ[A*, D] ≤ R[A*, D] ≤ (π/2)ρ[A*, D]
-- statement:
--   Let $A^*$ be a stable $n\times n$ matrix, $D\ne0$ an $n\times n$ matrix with nonnegative entries, $\mathcal D=\{(i,j):D_{ij}>0\}$, $E^{ij}$ the basic matrices, and $\rho\ge0$. Let $(\mathrm{Ly}[\rho])$ be the semi-infinite system $X\succeq I$, $A^TX+XA\preceq-I$ for all $A$ in the interval matrix $\mathcal U_\rho=\{A:|A_{ij}-A^*_{ij}|\le\rho D_{ij}\}$, and $(\mathrm A[\rho])$ the system of LMIs
--   $$X\succeq I,\quad X^{ij}\succeq\mp\rho D_{ij}\big[[E^{ij}]^TX+XE^{ij}\big]\ \ ((i,j)\in\mathcal D),\quad \sum_{(i,j)\in\mathcal D}X^{ij}\preceq-I-[A^*]^TX-XA^* .$$
--   Then:
--
--   1. If $(X,(X^{ij}))$ solves $(\mathrm A[\rho])$, then $X$ solves $(\mathrm{Ly}[\rho])$; in particular $(\mathrm{Ly}[\rho])$ is solvable whenever $(\mathrm A[\rho])$ is.
--   2. If $(\mathrm A[\rho])$ is not solvable, then $(\mathrm{Ly}[\pi\rho/2])$ is not solvable either.
--   3. Consequently, with $\rho[A^*,D]$ and $R[A^*,D]$ the suprema of those $\rho\ge0$ for which $(\mathrm A[\rho])$, resp. $(\mathrm{Ly}[\rho])$, is solvable,
--   $$\rho[A^*,D]\le R[A^*,D]\le\frac{\pi}{2}\,\rho[A^*,D].$$
--
--   This is the Matrix Cube Theorem applied with rank-two perturbations: the largest interval uncertainty level admitting a common quadratic Lyapunov function is computable by semidefinite programming within the factor $\pi/2$.
--
--   **Formalization Note** "Then so is the system $(\mathrm{Ly}[\pi\rho/2])$" in the book's (ii) means "$(\mathrm{Ly}[\pi\rho/2])$ is not solvable either", which is what is stated. The suprema are in `EReal`; the inequality chain is part of the statement for every $\rho\ge0$ (it does not depend on $\rho$). Stability of $A^*$ and $D\ne0$ are the standing assumptions of the problem Interval Lyapunov (p. 194).
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 195, Proposition 4.4.6 (problem Interval Lyapunov, p. 194)

import Mathlib
import Definitions.Def_ModernConvex_MatrixCube_IntervalLyapunov

open Matrix

namespace ModernConvex.MatrixCube

/-- Ben-Tal–Nemirovski, Proposition 4.4.6, p. 195 (Interval Lyapunov, p. 194): let `A*` be a
stable `n × n` matrix, `D ≠ 0` an `n × n` matrix with nonnegative entries, and `ρ ≥ 0`. Then
(i) if `(X, (Xⁱʲ))` solves the system of LMIs `(A[ρ])`, then `X` solves `(Ly[ρ])` (so `(Ly[ρ])`
is solvable whenever `(A[ρ])` is);
(ii) if `(A[ρ])` is not solvable, then `(Ly[πρ/2])` is not solvable either.
In particular `ρ[A*, D] ≤ R[A*, D] ≤ (π/2) ρ[A*, D]`, where `ρ[A*, D]` and `R[A*, D]` are the
suprema (in `[−∞, +∞]`) of the `ρ ≥ 0` for which `(A[ρ])`, resp. `(Ly[ρ])`, is solvable. -/
theorem interval_lyapunov {n : ℕ} (Astar D : Matrix (Fin n) (Fin n) ℝ) (hstab : IsStable Astar)
    (hD : D ≠ 0) (hDnn : ∀ i j, 0 ≤ D i j) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (∀ (X : Matrix (Fin n) (Fin n) ℝ) (Y : Fin n → Fin n → Matrix (Fin n) (Fin n) ℝ),
        IsASolution Astar D ρ X Y → IsLySolution Astar D ρ X) ∧
    (ASolvable Astar D ρ → LySolvable Astar D ρ) ∧
    (¬ ASolvable Astar D ρ → ¬ LySolvable Astar D (Real.pi * ρ / 2)) ∧
    lmiRadius Astar D ≤ lyapRadius Astar D ∧
    lyapRadius Astar D ≤ ((Real.pi / 2 : ℝ) : EReal) * lmiRadius Astar D := by sorry

end ModernConvex.MatrixCube
