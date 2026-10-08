-- Prove2me | Theorems.Thm_GomoryGroup_Rel_ip_le_lp_add_group
-- name    : GomoryGroup.Rel.ip_le_lp_add_group
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:30:16.248593+00:00
-- url     : https://prove2.me/theorems/9db277df-d49e-4f18-8eaf-2a23e40c98ab
-- title:
--   (7), proof of THEOREM 1, p. 263 — every feasible solution of P2 costs at most c_B B⁻¹b + φ(b)
-- statement:
--   Let $B$ be a nonsingular integer $m\times m$ matrix, $N$ an integer $m\times n$ matrix, $c_B\in\mathbb R^m$, $c_N\in\mathbb R^n$ and $b\in\mathbb Z^m$. Suppose the group problem (4) for $b$ attains its maximum value $\varphi(b)$. Then every feasible solution $(x_B,x_N)$ of P2 (integer, nonnegative, $Bx_B+Nx_N=b$) satisfies
--   $$c_Bx_B+c_Nx_N\le c_BB^{-1}b+\varphi(b).$$
--
--   With $c_BB^{-1}b=z_1(b)$ this is the paper's inequality (7), $z_2(b)\le z_1(b)+\varphi(b)$: the group problem is a relaxation of P2.
--
--   **Formalization Note** $\varphi(b)$ is assumed to be the greatest element of the set of objective values of (4), not a supremum. The paper's $z_1(b)$ is written $c_BB^{-1}b$, so the statement needs neither optimality of $B$ nor $b\in K^B$.
-- source:
--   Gomory, On the relation between integer and noninteger solutions to linear programs, Proc. Natl. Acad. Sci. USA 53 (1965), p. 263, (7)

import Mathlib
import Definitions.Def_GomoryGroup_Rel_Setting

namespace GomoryGroup.Rel

open Matrix

theorem ip_le_lp_add_group {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ)
    (hB : B.det ≠ 0) :
    ∀ φ : ℝ, IsGreatest (groupValues B N cB cN b) φ →
      ∀ (xB : Fin m → ℕ) (xN : Fin n → ℕ), IsIPFeasible B N b xB xN →
        ipCost cB cN xB xN ≤ cB ⬝ᵥ ((Br B)⁻¹ *ᵥ (fun i => (b i : ℝ))) + φ := by sorry

end GomoryGroup.Rel
