-- Prove2me | Theorems.Thm_KumarSeidman_TwoType_example2_modes_coexist
-- name    : KumarSeidman.TwoType.example2_modes_coexist
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:27:46.575161+00:00
-- url     : https://prove2.me/theorems/a9fec055-5e69-40f9-ad4e-cbbc95d0bd9d
-- title:
--   Example 2, p. 293 — the same system has a bounded and an unbounded clearing trajectory
-- statement:
--   Consider the system of Example 2: two part types with input rate $1$, part type 1 visiting buffer 1 at machine 1 and then buffer 2 at machine 2, part type 2 visiting buffer 3 at machine 2 and then buffer 4 at machine 1. Processing times $\tau_1,\dots,\tau_4$ and set-up times $\delta_1,\dots,\delta_4$ are positive, and they satisfy
--   $$
--   \tau_2+\tau_4>1, \tag{7}
--   $$
--   $$
--   \frac{\delta_1+\delta_4}{1-\tau_1-\tau_4}=\frac{\delta_2+\delta_3}{1-\tau_2-\tau_3}=:\eta, \tag{8}
--   $$
--   $$
--   \delta_4<(1-\tau_3-\tau_4)\eta, \tag{9}
--   $$
--   $$
--   \delta_2<(1-\tau_1-\tau_2)\eta, \tag{10}
--   $$
--   and the capacity condition (1), $\tau_1+\tau_4<1$ and $\tau_2+\tau_3<1$. Then, under the clearing policy:
--
--   1. **(stable mode)** From $x(0)=(0,\eta,0,\eta)$ with machine 1 set up for buffer 1 and machine 2 for buffer 3, a clearing trajectory exists, and every clearing trajectory from this state keeps every buffer level bounded on $[0,\infty)$.
--   2. **(unstable mode)** There is $\xi_0$ such that for every $\xi\ge\xi_0$, from $x(0)=(\xi,0,0,0)$ with machine 1 set up for buffer 4 and machine 2 for buffer 3, a clearing trajectory exists, and every clearing trajectory from this state has
--   $$
--   \sup_{0\le t<\infty}x_1(t)=+\infty .
--   $$
--
--   Thus the same system possesses both stable and unstable modes of behaviour, depending only on the initial state, and the instability arises although no part type revisits a machine.
--
--   **Formalization Note** Both modes assert existence of a clearing trajectory, so neither half holds vacuously. Stability and unboundedness are the paper's $\sup_{0\le t<\infty}x_{p,i}(t)<+\infty$ and its negation for buffer 1 (the paper writes $\limsup_t x_1(t)=+\infty$, equivalent for these continuous levels). The bound in the stable mode may depend on the trajectory. $\eta$ is computed from the data as $(\delta_1+\delta_4)/(1-\tau_1-\tau_4)$.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, pp. 292–293, Example 2 (conclusion, p. 293)

import Mathlib
import Definitions.Def_KumarSeidman_TwoType_Example2

namespace KumarSeidman.TwoType

open Example2

/-- Example 2 (pp. 292–293): for one system satisfying (7)–(10) and the capacity condition (1),
the clearing policy has both a stable and an unstable mode.

* From `x(0) = (0, η, 0, η)` with machines 1, 2 set up for buffers 1, 3, a clearing trajectory
  exists and every clearing trajectory keeps all buffer levels bounded.
* For every large enough `ξ`, from `x(0) = (ξ, 0, 0, 0)` with machines 1, 2 set up for
  buffers 4, 3, a clearing trajectory exists and every clearing trajectory has `x₁` unbounded
  on `[0, ∞)`. -/
theorem example2_modes_coexist (τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ)
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) (hτ₃ : 0 < τ₃) (hτ₄ : 0 < τ₄)
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃) (hδ₄ : 0 < δ₄)
    (h7 : τ₂ + τ₄ > 1)
    (h8 : (δ₁ + δ₄) / (1 - τ₁ - τ₄) = (δ₂ + δ₃) / (1 - τ₂ - τ₃))
    (h9 : δ₄ < (1 - τ₃ - τ₄) * ((δ₁ + δ₄) / (1 - τ₁ - τ₄)))
    (h10 : δ₂ < (1 - τ₁ - τ₂) * ((δ₁ + δ₄) / (1 - τ₁ - τ₄)))
    (h1₁ : τ₁ + τ₄ < 1) (h1₂ : τ₂ + τ₃ < 1) :
    let η := (δ₁ + δ₄) / (1 - τ₁ - τ₄)
    ((∃ T : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Schedule,
        T.IsClearingFrom (levels 0 η 0 η) (setups b₁ b₃)) ∧
      ∀ T : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Schedule,
        T.IsClearingFrom (levels 0 η 0 η) (setups b₁ b₃) → T.IsBounded) ∧
    ∃ ξ₀ : ℝ, ∀ ξ ≥ ξ₀,
      (∃ T : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Schedule,
          T.IsClearingFrom (levels ξ 0 0 0) (setups b₄ b₃)) ∧
        ∀ T : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Schedule,
          T.IsClearingFrom (levels ξ 0 0 0) (setups b₄ b₃) →
            ¬ BddAbove (T.x b₁ '' Set.Ici 0) := by sorry

end KumarSeidman.TwoType
