-- Prove2me | Theorems.Thm_KumarSeidman_TwoType_example2_periodic_trajectory_exists
-- name    : KumarSeidman.TwoType.example2_periodic_trajectory_exists
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-06T09:18:43.023223+00:00
-- url     : https://prove2.me/theorems/366a55b4-a09a-48fd-a9dc-fd9923e7f99c
-- title:
--   Example 2, Case 1, p. 293 — a clearing trajectory from x(0) = (0, η, 0, η) exists
-- statement:
--   Consider the system of Example 2. There are two part types, each with input rate $1$. Part type 1 visits buffer 1 at machine 1 and then buffer 2 at machine 2. Part type 2 visits buffer 3 at machine 2 and then buffer 4 at machine 1. The processing times $\tau_1,\dots,\tau_4$ and the set-up times $\delta_1,\dots,\delta_4$ are positive. Assume the capacity condition (1), $\tau_1+\tau_4<1$ and $\tau_2+\tau_3<1$, together with conditions (8)–(10):
--   $$
--   \frac{\delta_1+\delta_4}{1-\tau_1-\tau_4}=\frac{\delta_2+\delta_3}{1-\tau_2-\tau_3}=:\eta,\qquad
--   \delta_4<(1-\tau_3-\tau_4)\eta,\qquad \delta_2<(1-\tau_1-\tau_2)\eta .
--   $$
--   Then there exists a fluid trajectory of the system that follows the clearing policy and starts from
--   $$
--   x(0)=(0,\eta,0,\eta),
--   $$
--   with machine 1 set up for buffer 1 and machine 2 set up for buffer 3.
--
--   This is the existence half of the paper's Case 1 ("a periodic regime"). The paper describes this trajectory explicitly. Each machine first serves its nonempty buffer (buffer 4, resp. buffer 2), then returns to its first-stage buffer, and the state $(0,\eta,0,\eta)$ recurs at $t=\eta,2\eta,\dots$. Together with the milestone `case1_periodic` (every clearing trajectory from this state returns to it at time $\eta$), it gives the stable mode of Example 2.
--
--   **Formalization Note** "Fluid trajectory following the clearing policy" is the series' `IsClearingFrom` predicate: the trajectory axioms of `Def_KumarSeidman_TwoType_Trajectory` together with the clearing rule of Definition 1. The value $\eta$ is computed from the data as $(\delta_1+\delta_4)/(1-\tau_1-\tau_4)$.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, pp. 292–293, Example 2, Case 1 (a periodic regime), p. 293

import Mathlib
import Definitions.Def_KumarSeidman_TwoType_Example2

namespace KumarSeidman.TwoType

open Example2

/-- Example 2, Case 1 (p. 293): under (8)–(10) and the capacity condition (1), a clearing
trajectory starting from `x(0) = (0, η, 0, η)` with machines 1, 2 set up for buffers 1, 3
exists. -/
theorem example2_periodic_trajectory_exists (τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ)
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) (hτ₃ : 0 < τ₃) (hτ₄ : 0 < τ₄)
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃) (hδ₄ : 0 < δ₄)
    (h8 : (δ₁ + δ₄) / (1 - τ₁ - τ₄) = (δ₂ + δ₃) / (1 - τ₂ - τ₃))
    (h9 : δ₄ < (1 - τ₃ - τ₄) * ((δ₁ + δ₄) / (1 - τ₁ - τ₄)))
    (h10 : δ₂ < (1 - τ₁ - τ₂) * ((δ₁ + δ₄) / (1 - τ₁ - τ₄)))
    (h1₁ : τ₁ + τ₄ < 1) (h1₂ : τ₂ + τ₃ < 1) :
    let η := (δ₁ + δ₄) / (1 - τ₁ - τ₄)
    ∃ T : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Schedule,
      T.IsClearingFrom (levels 0 η 0 η) (setups b₁ b₃) := by sorry

end KumarSeidman.TwoType
