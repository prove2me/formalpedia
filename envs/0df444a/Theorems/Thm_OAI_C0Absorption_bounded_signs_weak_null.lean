-- Prove2me | Theorems.Thm_OAI_C0Absorption_bounded_signs_weak_null
-- name    : OAI.C0Absorption.bounded_signs_weak_null
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T21:57:25.070969+00:00
-- url     : https://prove2.me/theorems/396da909-b921-483c-b0d1-6f7b2af215b6
-- title:
--   Sequences with bounded signed sums are weakly null
-- statement:
--   Let $(m_i)$ be a sequence in a real normed space $X$ such that all signed partial sums are bounded:
--   $$
--   \Bigl\|\sum_{i<n}\pm m_i\Bigr\|\le M\qquad\text{for all }n\text{ and all signs}.
--   $$
--   Then $u(m_i)\to0$ for every continuous linear functional $u$ on $X$.
--
--   The unit vector basis of $c_0$ is the model: its signed sums are bounded and it is weakly null.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Pairings.lean#L239-L263

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings

open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset

theorem OAI.C0Absorption.bounded_signs_weak_null {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (m : ℕ → X) (M : ℝ)
    (hsum : ∀ n (ε : Fin n → Bool), ‖∑ i, realSign (ε i) • m i‖ ≤ M)
    (u : X →L[ℝ] ℝ) : Filter.Tendsto (fun i => u (m i)) Filter.atTop (nhds 0) := by sorry
