-- Prove2me | Theorems.Thm_KumarSeidman_TwoType_case2_stage8
-- name    : KumarSeidman.TwoType.case2_stage8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:29:09.068899+00:00
-- url     : https://prove2.me/theorems/ea050125-09c5-4a81-af76-7bc980eec2b0
-- title:
--   Example 2, Case 2, Stage 8, p. 293 — machine 2 clears buffer 2 at $t_9$ with $x(t_9)=(0,0,t_9-\delta_1,0)$
-- statement:
--   Consider the system of Example 2 with positive processing times $\tau_1,\dots,\tau_4$ and positive set-up times $\delta_1,\dots,\delta_4$. Assume (7), $\tau_2+\tau_4>1$, and the capacity condition (1), $\tau_1+\tau_4<1$ and $\tau_2+\tau_3<1$.
--
--   Start at $t_1=0$ from $x(0)=(\xi,0,0,0)$, with machine 1 set up for buffer 4 and machine 2 set up for buffer 3. There is $\xi_0$ such that for every $\xi\ge\xi_0$ every clearing trajectory from this state satisfies, with
--   $$
--   t_9=\frac{\xi+\tau_2^{-1}(\delta_1+\delta_2)}{\tau_2^{-1}-1},
--   $$
--   the identity
--   $$
--   x(t_9)=(0,\,0,\,t_9-\delta_1,\,0),
--   $$
--   and at $t_9$ machine 1 is set up for buffer 1 and machine 2 is set up for buffer 2 (which it has just cleared).
--
--   The state at $t_9$ is the mirror image of the initial state: the role of buffers 1, 2 and machine 1 is now played by buffers 3, 4 and machine 2. The level of buffer 3 is $t_9-\delta_1$, the amount that arrived since machine 2 last served it.
--
--   **Formalization Note** The paper's $t_1$ is $0$. "$\xi$ large enough" is rendered as $\exists\xi_0\,\forall\xi\ge\xi_0$. Conditions (8)–(10) are not assumed (the paper states they are unnecessary for Case 2). The denominator $\tau_2^{-1}-1$ is positive because $\tau_2<1$ by (1).
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 293, Example 2, Case 2, Stage 8

import Mathlib
import Definitions.Def_KumarSeidman_TwoType_Example2

namespace KumarSeidman.TwoType

open Example2

/-- Example 2, Case 2, Stage 8 (p. 293): under (7) and the capacity condition (1), for every
large enough `ξ`, every clearing trajectory from `x(0) = (ξ, 0, 0, 0)` with machine 1 set up
for buffer 4 and machine 2 for buffer 3 reaches at
`t₉ = (ξ + τ₂⁻¹(δ₁ + δ₂))/(τ₂⁻¹ − 1)` the state `x(t₉) = (0, 0, t₉ − δ₁, 0)`, with machine 1
set up for buffer 1 and machine 2 for buffer 2. -/
theorem case2_stage8 (τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ)
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) (hτ₃ : 0 < τ₃) (hτ₄ : 0 < τ₄)
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃) (hδ₄ : 0 < δ₄)
    (h7 : τ₂ + τ₄ > 1) (h1₁ : τ₁ + τ₄ < 1) (h1₂ : τ₂ + τ₃ < 1) :
    ∃ ξ₀ : ℝ, ∀ ξ ≥ ξ₀, ∀ T : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Schedule,
      T.IsClearingFrom (levels ξ 0 0 0) (setups b₄ b₃) →
        let t₉ := (ξ + τ₂⁻¹ * (δ₁ + δ₂)) / (τ₂⁻¹ - 1)
        (∀ b, T.x b t₉ = levels 0 0 (t₉ - δ₁) 0 b) ∧ T.SetupFor m₁ t₉ b₁ ∧
          T.SetupFor m₂ t₉ b₂ := by sorry

end KumarSeidman.TwoType
