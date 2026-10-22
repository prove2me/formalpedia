-- Prove2me | Theorems.Thm_ModernOnlineLearning_LowerBounds_phi_properties
-- name    : ModernOnlineLearning.LowerBounds.phi_properties
-- status  : Proved
-- author  : @suzukasan
-- created : 2026-10-21T08:24:36.8045+00:00
-- url     : https://prove2.me/theorems/81ad8308-c173-4ca5-be70-9b6d9ee1eff3
-- title:
--   Theorem 5.4 coefficient: positive range and limit 1 − log 2
-- statement:
--   For $0<\alpha<1$, let
--   $$\phi(\alpha)=\frac{1}{2-\alpha}+\frac{2^{\alpha-1}-1}{1-\alpha}.$$
--   The coefficient in the unprojected online subgradient descent lower bound satisfies
--   $$0<\phi(\alpha)<1-\log 2,$$
--   and
--   $$\lim_{\alpha\uparrow1}\phi(\alpha)=1-\log 2\ge\frac{3}{10}.$$
--   This formalizes the range and endpoint-limit assertions accompanying Theorem 5.4. The existing theorem `ModernOnlineLearning.LowerBounds.theorem_5_4` formalizes the adversarial sequence and regret estimate and explicitly leaves the endpoint limit outside its declaration. The limit here is from below, respecting the source domain $(0,1)$; it is not an assertion about the value of Lean's totalized formula at $\alpha=1$.
-- source:
--   Francesco Orabona, A Modern Introduction to Online Learning, arXiv:1912.13213v10, Theorem 5.4, printed p. 52, coefficient codomain and final sentence. https://arxiv.org/abs/1912.13213v10

import Mathlib
import Definitions.Def_ModernOnlineLearning_LowerBounds_phi
set_option autoImplicit false
open Filter Set
open scoped Topology

namespace ModernOnlineLearning.LowerBounds

/-- Coefficient range and endpoint limit accompanying Theorem 5.4, p. 52. -/
theorem phi_properties :
    (∀ α : ℝ, 0 < α → α < 1 → phi α ∈ Set.Ioo 0 (1-Real.log 2)) ∧
    Tendsto phi (𝓝[<] (1 : ℝ)) (𝓝 (1-Real.log 2)) ∧
    (3/10 : ℝ) ≤ 1-Real.log 2 := by sorry

end ModernOnlineLearning.LowerBounds
