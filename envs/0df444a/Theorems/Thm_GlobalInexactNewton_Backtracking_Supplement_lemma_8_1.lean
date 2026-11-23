-- Prove2me | Theorems.Thm_GlobalInexactNewton_Backtracking_Supplement_lemma_8_1
-- name    : GlobalInexactNewton.Backtracking.Supplement.lemma_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T08:57:45.656382+00:00
-- url     : https://prove2.me/theorems/12c6d4e6-0e17-4d83-9273-d1588014be7b
-- title:
--   Lemma 8.1 — Exact square-root parametrization of residual norm along a segment joining nested-space residual minimizers.
-- statement:
--   Let $A$ be a linear map, $b$ a right-hand side, and $u_0$ an initial approximation in a finite-dimensional real inner product space. Let $K_i\subseteq K_j$, and let $z_i,z_j$ minimize the residual norm over their respective subspaces. Put $\rho_i=\|b-A(u_0+z_i)\|$ and $\rho_j=\|b-A(u_0+z_j)\|$, and assume $\rho_i>\rho_j$. With $\tau(\rho)=\sqrt{(\rho^2-\rho_j^2)/(\rho_i^2-\rho_j^2)}$ and $z(\rho)=\tau(\rho)z_i+(1-\tau(\rho))z_j$, one has
--
--   $$\|b-A(u_0+z(\rho))\|=\rho\quad(\rho_j\le\rho\le\rho_i).$$
--
--   This parametrizes the spatial segment by its exact residual norm, without invertibility, uniqueness or solvability assumptions.
--
--   **Formalization Note** A finite-dimensional real inner product space represents the paper’s inner product geometry. The linear map $A$ is a continuous linear map; no nonlinear function or continuous-differentiability hypothesis is part of this lemma. The two nested subspaces and their attained minimizers make the preceding section’s context explicit.
--
--   Differences from the source:
--   - encoding: Two residual-minimizing stages in nested subspaces of real n-dimensional space with an inner product norm. → Two nested real submodules, a continuous linear map A, and explicit attained residual-minimizer predicates in a finite-dimensional real inner product space.; reason: These directly express the governing definitions on p. 415 without adding solvability, invertibility or uniqueness.
-- source:
--   Eisenstat and Walker, Globally Convergent Inexact Newton Methods, SIAM J. Optim. 4(2) (1994), p. 416, Lemma 8.1; DOI 10.1137/0804022

import Mathlib
import Definitions.Def_GlobalInexactNewton_Backtracking_Method
import Definitions.Def_GlobalInexactNewton_Backtracking_Supplement_ResidualMinimizer

namespace GlobalInexactNewton.Backtracking.Supplement

open Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem lemma_8_1 (A : E →L[ℝ] E) (b u₀ zi zj : E)
    (Ki Kj : Submodule ℝ E) (hsub : Ki ≤ Kj)
    (hi : IsResidualMinimizer A b u₀ Ki zi) (hj : IsResidualMinimizer A b u₀ Kj zj)
    (hρ : ‖b - A (u₀ + zj)‖ < ‖b - A (u₀ + zi)‖) :
    ∀ ρ ∈ Set.Icc ‖b - A (u₀ + zj)‖ ‖b - A (u₀ + zi)‖,
      ‖b - A (u₀ + residualSegment A b u₀ zi zj ρ)‖ = ρ := by sorry

end GlobalInexactNewton.Backtracking.Supplement
