-- Prove2me | Theorems.Thm_GomoryGroup_Rel_extend_group_solution
-- name    : GomoryGroup.Rel.extend_group_solution
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T08:30:37.422983+00:00
-- url     : https://prove2.me/theorems/e93b6c54-b7f3-44ac-98c0-c77b87482989
-- title:
--   proof of THEOREM 1, p. 263 — x_B = B⁻¹(b − Ny) is integral; if also x_B ≥ 0, (x_B, y) is optimal for P2 with cost z₁ + φ
-- statement:
--   Let $B$ be a nonsingular integer $m\times m$ matrix, $N$ an integer $m\times n$ matrix, $c_B\in\mathbb R^m$, $c_N\in\mathbb R^n$, $b\in\mathbb Z^m$, and let $y\in\mathbb N^n$ be an optimal solution of the group problem (4). Then:
--
--   1. $x_B=B^{-1}(b-Ny)$ is integral: there is $k\in\mathbb Z^m$ with $Bk=b-Ny$;
--   2. if moreover $k\ge0$, then $(x_B,y)=(k,y)$ is an optimal solution of P2, and its cost is
--   $$c_Bk+c_Ny=c_BB^{-1}b+\sum_{i=1}^nc^*_{i+m}y_i .$$
--
--   This is the extension step of the proof of THEOREM 1: a solution of the group problem whose basic part comes out nonnegative is already an optimal integer solution.
--
--   **Formalization Note** The nonnegative integer vector $k$ is turned into a vector of natural numbers coordinatewise. The paper's $z_1(b)$ appears as $c_BB^{-1}b$, and its $\varphi(b)$ as the objective value of the given optimal $y$.
-- source:
--   Gomory, On the relation between integer and noninteger solutions to linear programs, Proc. Natl. Acad. Sci. USA 53 (1965), p. 263, after (7)

import Mathlib
import Definitions.Def_GomoryGroup_Rel_Setting

namespace GomoryGroup.Rel

open Matrix

theorem extend_group_solution {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ)
    (N : Matrix (Fin m) (Fin n) ℤ) (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ)
    (hB : B.det ≠ 0) :
    ∀ y : Fin n → ℕ, IsGroupOptimal B N cB cN b y →
      ∃ k : Fin m → ℤ, B *ᵥ k = b - N *ᵥ (fun j => (y j : ℤ)) ∧
        (0 ≤ k →
          IsIPOptimal B N cB cN b (fun i => (k i).toNat) y ∧
            ipCost cB cN (fun i => (k i).toNat) y =
              cB ⬝ᵥ ((Br B)⁻¹ *ᵥ (fun i => (b i : ℝ))) + groupObj B N cB cN y) := by sorry

end GomoryGroup.Rel
