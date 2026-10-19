-- Prove2me | Theorems.Thm_MIPRE_Introspection_adaptiveFailureBudget_le_power
-- name    : MIPRE.Introspection.adaptiveFailureBudget_le_power
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:09:17.350962+00:00
-- url     : https://prove2.me/theorems/4a4e751f-3fe1-4379-893b-bc9e15dec5c7
-- title:
--   The actual finite recurrence has exponent 8^(-n)
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.AdaptivePowerBudget` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Power bounds for the full finite adaptive recurrence. Each replacement introduces three square roots. For any fixed number of replacements the actual failure recurrence is bounded by an explicit constant times the corresponding iterated root of a common primitive error. A second explicit coefficient makes this bound at least one outside the proved admissible small-error regime. These numerical statements do not assume the existence or soundness of the strategy construction.
--
--   The actual finite recurrence has exponent `8^(-n)`. This estimate has
--   no stage-admissibility premise and works for any fixed number of steps,
--   including two full local iterations.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--
--   theorem MIPRE.Introspection.adaptiveFailureBudget_le_power (r n : ℕ) {edges z h initial t : ℝ}
--       (hE : 0 ≤ edges) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
--       (hi : initial ≤ t) (hz : z ≤ t) (hh : h ≤ t) :
--       adaptiveFailureBudget r edges z h initial n ≤
--         adaptivePowerCoefficient r edges ^ n * iteratedRoot (3 * n) t
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.adaptiveFailureBudget_le_power` is declared in `MIPRE/Foundations/Introspection/AdaptivePowerBudget.lean`, lines 96–147. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AdaptivePowerBudget.lean#L96-L147; blueprint lem:intro-recurrence-power

import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Introspection_ErrorBounds
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveStageBudget
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveIterationBudget
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptivePowerBudget

open MIPRE
open MIPRE.Introspection

theorem MIPRE.Introspection.adaptiveFailureBudget_le_power (r n : ℕ) {edges z h initial t : ℝ}
    (hE : 0 ≤ edges) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hi : initial ≤ t) (hz : z ≤ t) (hh : h ≤ t) :
    adaptiveFailureBudget r edges z h initial n ≤
      adaptivePowerCoefficient r edges ^ n * iteratedRoot (3 * n) t := by sorry
