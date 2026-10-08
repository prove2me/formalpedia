-- Prove2me | Theorems.Thm_MazurHuang_exists_tate_normal_form_of_addOrderOf_gt_three
-- name    : MazurHuang.exists_tate_normal_form_of_addOrderOf_gt_three
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-06T14:13:40.807339+00:00
-- url     : https://prove2.me/theorems/4644a6de-e3d2-4192-bdd2-a21c867aacba
-- title:
--   Tate normal form: a rational point of order $n>3$ can be moved to $(0,0)$ on $y^2+(1-c)xy-by=x^3-bx^2$
-- statement:
--   Let $E$ be an elliptic curve over $\mathbb{Q}$, given by a Weierstrass equation, and let $P \in E(\mathbb{Q})$ be a rational point of exact order $n$, where $n > 3$. Then there are rational numbers $b$ and $c$ with $b \neq 0$ such that the Weierstrass cubic
--
--   $$
--   E_{b,c} : \quad y^2 + (1-c)\,xy - b\,y = x^3 - b\,x^2
--   $$
--
--   is nonsingular (so it is an elliptic curve over $\mathbb{Q}$), and the point $(0,0) \in E_{b,c}(\mathbb{Q})$ has exact order $n$.
--
--   The curve $E_{b,c}$ is the Tate normal form attached to the pair $(E,P)$. The theorem reduces every question about a rational point of order $n > 3$ on an arbitrary elliptic curve to a question about the two rational parameters $(b,c)$; for each $n$ the condition that $(0,0)$ has order $n$ is then a polynomial equation in $b$ and $c$, which is an affine model of the modular curve $X_1(n)$. This is the first step of the classical treatment of each individual torsion order in Mazur's theorem.
--
--   **Formalization Note** $E_{b,c}$ is the Weierstrass curve with coefficients $(a_1,a_2,a_3,a_4,a_6) = (1-c,\,-b,\,-b,\,0,\,0)$; "nonsingular" is the `IsElliptic` class (invertible discriminant). The point $(0,0)$ is the affine point `Point.some 0 0 h`, where `h` is a proof that $(0,0)$ is a nonsingular point of the cubic, and "exact order $n$" is `addOrderOf … = n` in the Mordell–Weil group. The statement asserts only the existence of $(b,c)$ with these properties; it does not record the isomorphism between $E$ and $E_{b,c}$ that the proof constructs.
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT, commit 51bbb4f191ad0d3753b87123635c100a638ae580, branch verify-sorry-restore; Apache-2.0

import Mathlib

open scoped WeierstrassCurve.Affine

theorem MazurHuang.exists_tate_normal_form_of_addOrderOf_gt_three
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (P : (E⁄ℚ).Point) (n : ℕ) (hn : 3 < n)
    (hP : addOrderOf P = n) :
    ∃ b c : ℚ, b ≠ 0 ∧
      ({ a₁ := 1 - c, a₂ := -b, a₃ := -b, a₄ := 0, a₆ := 0 } : WeierstrassCurve ℚ).IsElliptic ∧
      ∃ h : ({ a₁ := 1 - c, a₂ := -b, a₃ := -b, a₄ := 0, a₆ := 0 } : WeierstrassCurve ℚ).toAffine.Nonsingular 0 0,
        addOrderOf (WeierstrassCurve.Affine.Point.some 0 0 h) = n := by sorry
