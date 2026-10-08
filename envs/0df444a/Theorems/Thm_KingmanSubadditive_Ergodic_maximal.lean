-- Prove2me | Theorems.Thm_KingmanSubadditive_Ergodic_maximal
-- name    : KingmanSubadditive.Ergodic.maximal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:41:59.242011+00:00
-- url     : https://prove2.me/theorems/609f4e32-f342-4a35-80db-4cece30dbc98
-- title:
--   (1.2.5): the maximal ergodic inequality
-- statement:
--   Let $x$ be a subadditive process and let $B$ be the event that $x_{0t}\ge0$ for at least one integer $t\ge1$. Then the maximal ergodic inequality quoted by Kingman is
--   $$\int_B x_{01}\,dP\ge0.$$
--   It constrains the first increment on the event where a nonnegative path value occurs and is one of the auxiliary results recorded alongside Theorem 1.
--
--   **Formalization Note** The paper prints a conditional-expectation bar. The integral has the same sign as that conditional expectation when $P(B)>0$, and remains meaningful when $P(B)=0$.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 885, (1.2.5)

import Mathlib
import Definitions.Def_KingmanSubadditive_Ergodic_Process

namespace KingmanSubadditive.Ergodic

open MeasureTheory

/-- Kingman, *Subadditive ergodic theory*, Ann. Probab. 1(6):883–899 (1973),
p. 885, (1.2.5), quoted from [8]. The printed conditional-expectation
notation is read as the integral over the event where some `x₀ₜ ≥ 0`;
it has the same sign when the event has positive probability and also
makes sense when its probability is zero. -/
theorem maximal {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (x : ℕ → ℕ → Ω → ℝ)
    (hx : IsSubadditiveProcess P x) :
    0 ≤ ∫ ω in {ω | ∃ t : ℕ, 1 ≤ t ∧ 0 ≤ x 0 t ω}, x 0 1 ω ∂P := by sorry

end KingmanSubadditive.Ergodic
