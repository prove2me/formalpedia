-- Prove2me | Theorems.Thm_GloriaOtto_Variance_corollary_2_3
-- name    : GloriaOtto.Variance.corollary_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:28.118212+00:00
-- url     : https://prove2.me/theorems/d2ae95b2-e3cf-4ea3-b322-a38423b25f5e
-- title:
--   Corollary 2.3 — |∇G_T(x, y; a)| ≲ 1 uniformly in a ∈ A_αβ, T > 0 and x, y
-- statement:
--   Let $d \ge 2$, $0 < \alpha \le \beta$. There is a constant $C$, depending only on $d, \alpha, \beta$, such that for every $a \in \mathcal A_{\alpha\beta}$, every $T > 0$ and all $x, y \in \mathbb Z^d$,
--   $$|\nabla_x G_T(x,y;a)| = \Big(\sum_{i=1}^d \big(G_T(x+e_i,y;a) - G_T(x,y;a)\big)^2\Big)^{1/2} \le C .$$
--
--   The bound uses the discreteness of the lattice; no such bound holds in the continuum.
--
--   **Formalization Note.** The gradient is taken in the first argument, as in the paper's proof (p. 61); the bound in the second argument follows from the symmetry $G_T(x,y) = G_T(y,x)$ and is not stated.
-- source:
--   Gloria, Otto, arXiv:1104.1291v1, Corollary 2.3, p. 20

import Mathlib
import Definitions.Def_GloriaOtto_Variance_Setup

open MeasureTheory ProbabilityTheory

namespace GloriaOtto.Variance

theorem corollary_2_3 (d : ℕ) (hd : 2 ≤ d) (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) :
    ∃ C : ℝ, ∀ a : Edge d → ℝ, InA α β a → ∀ T : ℝ, 0 < T → ∀ x y : Site d,
      Real.sqrt (sqNorm (fun i => greenT a T (x + unit i) y - greenT a T x y)) ≤ C := by sorry

end GloriaOtto.Variance
