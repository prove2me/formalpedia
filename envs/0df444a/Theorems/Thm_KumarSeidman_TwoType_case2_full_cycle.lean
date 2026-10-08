-- Prove2me | Theorems.Thm_KumarSeidman_TwoType_case2_full_cycle
-- name    : KumarSeidman.TwoType.case2_full_cycle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:55.014142+00:00
-- url     : https://prove2.me/theorems/c7423d9a-4c40-4a07-a4d1-6b8e4ed0bb31
-- title:
--   Example 2, Case 2, p. 293 (corrected) — at $t_{17}$, $x(t_{17})=(\lambda\xi+\alpha,0,0,0)$ with the initial set-ups
-- statement:
--   Consider the system of Example 2 with positive processing times $\tau_1,\dots,\tau_4$ and positive set-up times $\delta_1,\dots,\delta_4$. Assume (7), $\tau_2+\tau_4>1$, and the capacity condition (1), $\tau_1+\tau_4<1$ and $\tau_2+\tau_3<1$.
--
--   Start at $t_1=0$ from $x(0)=(\xi,0,0,0)$, with machine 1 set up for buffer 4 and machine 2 set up for buffer 3. Let
--   $$
--   t_9=\frac{\xi+\tau_2^{-1}(\delta_1+\delta_2)}{\tau_2^{-1}-1},\qquad
--   t_{17}=t_9+\frac{t_9-\delta_1+\tau_4^{-1}(\delta_3+\delta_4)}{\tau_4^{-1}-1},
--   $$
--   $$
--   \lambda=\frac{\tau_2\tau_4}{(1-\tau_2)(1-\tau_4)},\qquad
--   \alpha=\Big[\frac{\delta_1+\delta_2}{1-\tau_2}-\delta_1+\frac{1}{\tau_4}(\delta_3+\delta_4)\Big]\Big(\frac1{\tau_4}-1\Big)^{-1}-\delta_3 .
--   $$
--   There is $\xi_0$ such that for every $\xi\ge\xi_0$ every clearing trajectory from this state satisfies
--   $$
--   x(t_{17})=(\lambda\xi+\alpha,\,0,\,0,\,0),
--   $$
--   and at $t_{17}$ machine 1 is again set up for buffer 4 and machine 2 for buffer 3.
--
--   The situation at $t_{17}$ is the initial one with the level of buffer 1 multiplied by $\lambda$ and shifted by $\alpha$. Since $\lambda>1$ exactly when $\tau_2+\tau_4>1$, iterating this cycle makes $x_1$ grow without bound.
--
--   **Formalization Note** The printed constant $\alpha$ (p. 293) lacks the final $-\delta_3$. Mirroring Stage 8 (buffers $1\leftrightarrow3$, $2\leftrightarrow4$, machines $1\leftrightarrow2$) from the level $x_3(t_9)=t_9-\delta_1$ gives $x_1(t_{17})=\big(x_3(t_9)+\tau_4^{-1}(\delta_3+\delta_4)\big)/(\tau_4^{-1}-1)-\delta_3$, which is $\lambda\xi+\alpha$ with the corrected $\alpha$ above; an exact simulation of the sample parameters confirms it. The printed $\lambda$ is correct. The closed form of $t_{17}$ is the mirror of the paper's computation of $t_9$. The paper's $t_1$ is $0$, and "$\xi$ large enough" is rendered as $\exists\xi_0\,\forall\xi\ge\xi_0$.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 293, Example 2, Case 2 (display after Stage 8; α corrected)

import Mathlib
import Definitions.Def_KumarSeidman_TwoType_Example2

namespace KumarSeidman.TwoType

open Example2

/-- Example 2, Case 2, full cycle (p. 293, with the printed constant `α` corrected by `− δ₃`):
under (7) and the capacity condition (1), for every large enough `ξ`, every clearing trajectory
from `x(0) = (ξ, 0, 0, 0)` with machine 1 set up for buffer 4 and machine 2 for buffer 3 reaches
at `t₁₇ = t₉ + (t₉ − δ₁ + τ₄⁻¹(δ₃ + δ₄))/(τ₄⁻¹ − 1)` the state `x(t₁₇) = (λξ + α, 0, 0, 0)`,
again with machine 1 set up for buffer 4 and machine 2 for buffer 3. -/
theorem case2_full_cycle (τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ)
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) (hτ₃ : 0 < τ₃) (hτ₄ : 0 < τ₄)
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃) (hδ₄ : 0 < δ₄)
    (h7 : τ₂ + τ₄ > 1) (h1₁ : τ₁ + τ₄ < 1) (h1₂ : τ₂ + τ₃ < 1) :
    ∃ ξ₀ : ℝ, ∀ ξ ≥ ξ₀, ∀ T : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Schedule,
      T.IsClearingFrom (levels ξ 0 0 0) (setups b₄ b₃) →
        let t₉ := (ξ + τ₂⁻¹ * (δ₁ + δ₂)) / (τ₂⁻¹ - 1)
        let t₁₇ := t₉ + (t₉ - δ₁ + τ₄⁻¹ * (δ₃ + δ₄)) / (τ₄⁻¹ - 1)
        let lam := τ₂ * τ₄ / ((1 - τ₂) * (1 - τ₄))
        let α := ((δ₁ + δ₂) / (1 - τ₂) - δ₁ + (1 / τ₄) * (δ₃ + δ₄)) * ((1 / τ₄) - 1)⁻¹ - δ₃
        (∀ b, T.x b t₁₇ = levels (lam * ξ + α) 0 0 0 b) ∧ T.SetupFor m₁ t₁₇ b₄ ∧
          T.SetupFor m₂ t₁₇ b₃ := by sorry

end KumarSeidman.TwoType
