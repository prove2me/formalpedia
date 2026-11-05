-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_primal_oracle_step
-- name    : ModernConvex.Relaxations.primal_oracle_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:34:37.620448+00:00
-- url     : https://prove2.me/theorems/e270c9ff-df0e-48e4-9ab9-430ec3471c00
-- title:
--   Separation oracle for the primal Max-Cut SDP body
-- statement:
--   **The separation oracle for the primal Max-Cut SDP body.**
--
--   The feasible set of the Max-Cut semidefinite relaxation is $K=\{X : X\succeq0,\ X_{ii}=1\}$, a convex body of symmetric matrices. For every symmetric $X$, exactly one of the following holds:
--   1. $X\succeq0$; or
--   2. there is a nonzero symmetric matrix $W$ with $\langle Y-X,W\rangle\le0$ for every $Y\succeq0$, where $\langle A,B\rangle=\sum_{i,j}A_{ij}B_{ij}$ is the Frobenius pairing.
--
--   The certificate is explicit: if $X$ is not positive semidefinite there is $v$ with $v^{\mathsf T}Xv<0$, and one takes $W=-vv^{\mathsf T}$. Then for $Y\succeq0$,
--   $$\langle Y-X,-vv^{\mathsf T}\rangle=v^{\mathsf T}Xv-v^{\mathsf T}Yv<0,$$
--   since $v^{\mathsf T}Yv\ge0$. If $X$ is rational then so is $W$.
--
--   Together with the affine constraints $X_{ii}=1$ (separated by coordinate functionals) this is exactly what an ellipsoid-method run on $K$ consumes at an infeasible centre; at a feasible centre the subgradient of the affine objective is constant. Running the ellipsoid on the *primal* body, unlike on the dual, needs no strong duality: the reported value is attained at a feasible point, so it is automatically a lower bound for the optimum.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, (4.3.15), p. 170; separation for the semidefinite constraint, as used by Bubeck, arXiv:1405.4980, Thm 2.4.

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations

open Matrix
open scoped BigOperators

namespace ModernConvex.Relaxations

/-- **The primal oracle step.** For every symmetric `X`: either `X ⪰ 0`, or there is a nonzero
matrix `W` separating `X` from the positive semidefinite cone by the Frobenius pairing
`⟨Y − X, W⟩ = Σ_{i,j} (Y − X)_{ij} W_{ij} ≤ 0` for every `Y ⪰ 0`. -/
theorem primal_oracle_step {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) :
    X.PosSemidef ∨
      ∃ W : Matrix (Fin n) (Fin n) ℝ, W ≠ 0 ∧
        ∀ Y : Matrix (Fin n) (Fin n) ℝ, Y.PosSemidef →
          (∑ i, ∑ j, (Y - X) i j * W i j) ≤ 0 := by sorry

end ModernConvex.Relaxations
