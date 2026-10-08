-- Prove2me | Theorems.Thm_GomoryGroup_Rel_cost_identity
-- name    : GomoryGroup.Rel.cost_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:29:26.782536+00:00
-- url     : https://prove2.me/theorems/c9427544-21b0-4e31-9276-13ee9d7d2e8e
-- title:
--   (5)–(6), proof of THEOREM 1, p. 263 — c(x_B, x_N) = c_B B⁻¹b + Σ c*_i x_i on Bx_B + Nx_N = b
-- statement:
--   Let $B$ be a nonsingular integer $m\times m$ matrix, $N$ an integer $m\times n$ matrix, $c_B\in\mathbb R^m$, $c_N\in\mathbb R^n$ and $b\in\mathbb Z^m$. If real vectors $x_B\in\mathbb R^m$, $x_N\in\mathbb R^n$ satisfy (5), $Bx_B+Nx_N=b$, then
--   $$c_Bx_B+c_Nx_N=c_BB^{-1}b+(c_N-c_BB^{-1}N)x_N=c_BB^{-1}b+\sum_{i=m+1}^{m+n}c^*_ix_i,$$
--   where $c^*_{m+1+j}=c_{m+1+j}-c_BB^{-1}\alpha_{m+1+j}$ is the relative cost of the nonbasic column $j$ (the paper's $\alpha_{m+1+j}$ is column $j$ of $N$).
--
--   This expresses the cost of any solution of the equality system in terms of its nonbasic part only; with $c_BB^{-1}b=z_1(b)$ it is the paper's (6).
--
--   **Formalization Note** No sign condition on $x$ and no optimality of $B$ is needed, so neither is assumed; the paper's $z_1(b)$ appears as $c_BB^{-1}b$ (the referenced simplex optimality criterion identifies the two).
-- source:
--   Gomory, On the relation between integer and noninteger solutions to linear programs, Proc. Natl. Acad. Sci. USA 53 (1965), p. 263, (5) and (6)

import Mathlib
import Definitions.Def_GomoryGroup_Rel_Setting

namespace GomoryGroup.Rel

open Matrix

theorem cost_identity {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ) (hB : B.det ≠ 0) :
    ∀ (xB : Fin m → ℝ) (xN : Fin n → ℝ),
      Br B *ᵥ xB + Nr N *ᵥ xN = (fun i => (b i : ℝ)) →
        cB ⬝ᵥ xB + cN ⬝ᵥ xN =
          cB ⬝ᵥ ((Br B)⁻¹ *ᵥ (fun i => (b i : ℝ))) + ∑ j, reducedCost B N cB cN j * xN j := by sorry

end GomoryGroup.Rel
