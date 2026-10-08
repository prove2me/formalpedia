-- Prove2me | Theorems.Thm_MazurHuang_exists_tate_normal_form_with_j_of_addOrderOf_gt_three
-- name    : MazurHuang.exists_tate_normal_form_with_j_of_addOrderOf_gt_three
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-06T21:06:08.994197+00:00
-- url     : https://prove2.me/theorems/d896121f-b0e9-4f05-9595-f085b5fa85e1
-- title:
--   Tate normal form of a rational point of order greater than 3, with the same j-invariant
-- statement:
--   Let $E$ be an elliptic curve over $\mathbb{Q}$ and $P \in E(\mathbb{Q})$ a point of exact order $n > 3$. Then there are $b, c \in \mathbb{Q}$ with $b \neq 0$ such that the Tate normal form
--   $$E_{b,c} : y^2 + (1-c)xy - by = x^3 - bx^2$$
--   is an elliptic curve with $j(E_{b,c}) = j(E)$ on which $(0,0)$ is a point of exact order $n$.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT, commit 51bbb4f191ad0d3753b87123635c100a638ae580, branch verify-sorry-restore; Apache-2.0; scratch/TateZ2xZ10.lean, scratch/TateZ2xZ10Reduction.lean, FLT/Assumptions/MazurProof/TateNormalFormBridge.lean.

import Mathlib

open scoped WeierstrassCurve.Affine

theorem MazurHuang.exists_tate_normal_form_with_j_of_addOrderOf_gt_three
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (P : (E⁄ℚ).Point) (n : ℕ) (hn : 3 < n)
    (hP : addOrderOf P = n) :
    ∃ b c : ℚ, b ≠ 0 ∧
      ∃ _hEll : ({ a₁ := 1 - c, a₂ := -b, a₃ := -b, a₄ := 0, a₆ := 0 } : WeierstrassCurve ℚ).IsElliptic,
        ({ a₁ := 1 - c, a₂ := -b, a₃ := -b, a₄ := 0, a₆ := 0 } : WeierstrassCurve ℚ).j = E.j ∧
        ∃ h : ({ a₁ := 1 - c, a₂ := -b, a₃ := -b, a₄ := 0, a₆ := 0 } : WeierstrassCurve ℚ).toAffine.Nonsingular 0 0,
          addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 h) = n := by sorry
