-- Prove2me | Theorems.Thm_GloriaOtto_Variance_definition_2_7_green_exists_unique
-- name    : GloriaOtto.Variance.definition_2_7_green_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:07.955461+00:00
-- url     : https://prove2.me/theorems/3d903910-2419-47e2-ae76-3ebd0ba5274a
-- title:
--   Definition 2.7 — existence and uniqueness of the discrete Green's function G_T(·, y; a) in ℓ²(ℤ^d)
-- statement:
--   Let $d \ge 2$, $0 < \alpha \le \beta$, let $a \in \mathcal A_{\alpha\beta}$ be a conductivity function on $\mathbb Z^d$ and $T > 0$. For every pole $y \in \mathbb Z^d$ there is exactly one $g \in \ell^2(\mathbb Z^d)$ such that
--   $$\sum_{x\in\mathbb Z^d} T^{-1} g(x) v(x) + \sum_{x\in\mathbb Z^d}\nabla v(x)\cdot A(x)\nabla g(x) = v(y) \qquad\text{for all } v \in \ell^2(\mathbb Z^d).$$
--
--   This is the sentence following (2.11): the discrete Green's function $G_T(\cdot, y; a)$ is well defined. It shows that the mission's Green's function is the paper's $G_T$, and not the default value $0$.
-- source:
--   Gloria, Otto, arXiv:1104.1291v1, Definition 2.7 and the sentence following it, (2.11), p. 16

import Mathlib
import Definitions.Def_GloriaOtto_Variance_Setup

open MeasureTheory ProbabilityTheory

namespace GloriaOtto.Variance

theorem definition_2_7_green_exists_unique (d : ℕ) (hd : 2 ≤ d) (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) :
    ∀ a : Edge d → ℝ, InA α β a → ∀ T : ℝ, 0 < T → ∀ y : Site d,
      ∃! g : Site d → ℝ, IsGreen a T y g := by sorry

end GloriaOtto.Variance
