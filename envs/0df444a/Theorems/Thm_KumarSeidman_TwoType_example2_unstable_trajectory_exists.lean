-- Prove2me | Theorems.Thm_KumarSeidman_TwoType_example2_unstable_trajectory_exists
-- name    : KumarSeidman.TwoType.example2_unstable_trajectory_exists
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-06T09:18:48.44308+00:00
-- url     : https://prove2.me/theorems/a6e29ef9-7c33-4e3c-bc43-f38ff32dcdd0
-- title:
--   Example 2, Case 2, p. 293 — for large ξ a clearing trajectory from x(0) = (ξ, 0, 0, 0) exists
-- statement:
--   Consider the system of Example 2. There are two part types, each with input rate $1$. Part type 1 visits buffer 1 at machine 1 and then buffer 2 at machine 2. Part type 2 visits buffer 3 at machine 2 and then buffer 4 at machine 1. The processing times $\tau_1,\dots,\tau_4$ and the set-up times $\delta_1,\dots,\delta_4$ are positive. Assume (7), $\tau_2+\tau_4>1$, and the capacity condition (1), $\tau_1+\tau_4<1$ and $\tau_2+\tau_3<1$.
--
--   Then there is $\xi_0$ such that for every $\xi\ge\xi_0$ there exists a fluid trajectory of the system that follows the clearing policy and starts from
--   $$
--   x(0)=(\xi,0,0,0),
--   $$
--   with machine 1 set up for buffer 4 and machine 2 set up for buffer 3.
--
--   This is the existence half of the paper's Case 2 (the unstable mode). The paper describes this trajectory stage by stage (Stages 1–8 and their mirror image), and it repeats with the level of buffer 1 multiplied by $\lambda=\tau_2\tau_4/((1-\tau_2)(1-\tau_4))>1$ at each cycle. Together with the milestones `case2_stage8` and `case2_full_cycle`, it gives the unstable mode of Example 2.
--
--   **Formalization Note** "Fluid trajectory following the clearing policy" is the series' `IsClearingFrom` predicate. "$\xi$ large enough" is rendered as $\exists\xi_0\,\forall\xi\ge\xi_0$. Conditions (8)–(10) are not needed (the paper states they are unnecessary for Case 2).
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, pp. 292–293, Example 2, Case 2 (Stages 1–8 and the mirror stages), p. 293

import Mathlib
import Definitions.Def_KumarSeidman_TwoType_Example2

namespace KumarSeidman.TwoType

open Example2

/-- Example 2, Case 2 (pp. 292–293): under (7) and the capacity condition (1), for every large
enough `ξ` a clearing trajectory starting from `x(0) = (ξ, 0, 0, 0)` with machines 1, 2 set up
for buffers 4, 3 exists. -/
theorem example2_unstable_trajectory_exists (τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ)
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) (hτ₃ : 0 < τ₃) (hτ₄ : 0 < τ₄)
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃) (hδ₄ : 0 < δ₄)
    (h7 : τ₂ + τ₄ > 1) (h1₁ : τ₁ + τ₄ < 1) (h1₂ : τ₂ + τ₃ < 1) :
    ∃ ξ₀ : ℝ, ∀ ξ ≥ ξ₀, ∃ T : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Schedule,
      T.IsClearingFrom (levels ξ 0 0 0) (setups b₄ b₃) := by sorry

end KumarSeidman.TwoType
