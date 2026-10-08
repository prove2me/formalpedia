-- Prove2me | Theorems.Thm_KumarSeidman_TwoType_case1_periodic
-- name    : KumarSeidman.TwoType.case1_periodic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:02.942033+00:00
-- url     : https://prove2.me/theorems/4b6b190c-6d97-44cd-8792-33aa0a75335b
-- title:
--   Example 2, Case 1, p. 293 — from $x(0)=(0,\eta,0,\eta)$ the clearing trajectory returns to the same state at $t=\eta$
-- statement:
--   Consider the system of Example 2 with positive processing times $\tau_1,\dots,\tau_4$ and positive set-up times $\delta_1,\dots,\delta_4$. Assume the capacity condition (1), $\tau_1+\tau_4<1$ and $\tau_2+\tau_3<1$, and conditions (8)–(10):
--   $$
--   \frac{\delta_1+\delta_4}{1-\tau_1-\tau_4}=\frac{\delta_2+\delta_3}{1-\tau_2-\tau_3}=:\eta,\qquad
--   \delta_4<(1-\tau_3-\tau_4)\eta,\qquad \delta_2<(1-\tau_1-\tau_2)\eta .
--   $$
--   Consider a time $t=0$ at which buffers 1 and 3 have just been cleared: $x(0)=(0,\eta,0,\eta)$, machine 1 is set up for buffer 1 and machine 2 for buffer 3. Then every clearing trajectory from this state satisfies
--   $$
--   x(\eta)=(0,\eta,0,\eta),
--   $$
--   and at time $\eta$ machine 1 is again set up for buffer 1 and machine 2 for buffer 3.
--
--   The system therefore returns to its initial state at $t=\eta$, which gives a periodic regime in which all buffers stay bounded. Assumption (7) is not needed.
--
--   **Formalization Note** "Set up for $b$ at time $\eta$" means that the run of the machine that contains $\eta$ in its half-open interval $(s_k,s_{k+1}]$ is devoted to $b$. At $\eta$ both machines are about to commence a set-up, exactly as at $t=0$. $\eta$ is computed from the data as $(\delta_1+\delta_4)/(1-\tau_1-\tau_4)$; the denominators are positive by (1).
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 293, Example 2, Case 1

import Mathlib
import Definitions.Def_KumarSeidman_TwoType_Example2

namespace KumarSeidman.TwoType

open Example2

/-- Example 2, Case 1 (p. 293): under (8)–(10) and the capacity condition (1) (but not (7)),
starting at `t = 0` with `x(0) = (0, η, 0, η)` and machines 1, 2 set up for the just-cleared
buffers 1, 3, every clearing trajectory is back in the same state at `t = η`. -/
theorem case1_periodic (τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ)
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) (hτ₃ : 0 < τ₃) (hτ₄ : 0 < τ₄)
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃) (hδ₄ : 0 < δ₄)
    (h8 : (δ₁ + δ₄) / (1 - τ₁ - τ₄) = (δ₂ + δ₃) / (1 - τ₂ - τ₃))
    (h9 : δ₄ < (1 - τ₃ - τ₄) * ((δ₁ + δ₄) / (1 - τ₁ - τ₄)))
    (h10 : δ₂ < (1 - τ₁ - τ₂) * ((δ₁ + δ₄) / (1 - τ₁ - τ₄)))
    (h1₁ : τ₁ + τ₄ < 1) (h1₂ : τ₂ + τ₃ < 1)
    (T : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Schedule) :
    let η := (δ₁ + δ₄) / (1 - τ₁ - τ₄)
    T.IsClearingFrom (levels 0 η 0 η) (setups b₁ b₃) →
      (∀ b, T.x b η = levels 0 η 0 η b) ∧ T.SetupFor m₁ η b₁ ∧ T.SetupFor m₂ η b₃ := by sorry

end KumarSeidman.TwoType
