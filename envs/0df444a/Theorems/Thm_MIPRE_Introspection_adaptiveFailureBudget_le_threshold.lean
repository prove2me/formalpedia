-- Prove2me | Theorems.Thm_MIPRE_Introspection_adaptiveFailureBudget_le_threshold
-- name    : MIPRE.Introspection.adaptiveFailureBudget_le_threshold
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:57:07.370315+00:00
-- url     : https://prove2.me/theorems/595689d5-13cf-4697-b161-3faf3b2d3a05
-- title:
--   If all three initial errors fit the depth-N threshold, the failure after n replacements fits the threshold with N-n levels remaining
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.AdaptiveIterationBudget` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). A positive small-error threshold for every adaptive stage. The failure recurrence has an explicit inverse threshold. For any fixed depth and number of replacements, sufficiently small initial and primitive errors keep every common stage budget at most one. The construction uses the proved triple-square-root replacement loss; no stage-smallness premise is built into the threshold.
--
--   If all three initial errors fit the depth-N threshold, the failure
--   after n replacements fits the threshold with N-n levels remaining.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--
--   theorem MIPRE.Introspection.adaptiveFailureBudget_le_threshold (r N : ℕ) {edges z h initial : ℝ}
--       (hE : 0 ≤ edges) (hi : initial ≤ adaptiveSmallThreshold r edges N)
--       (hz : z ≤ adaptiveSmallThreshold r edges N)
--       (hh : h ≤ adaptiveSmallThreshold r edges N) :
--       ∀ n, n ≤ N → adaptiveFailureBudget r edges z h initial n ≤
--         adaptiveSmallThreshold r edges (N - n)
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.adaptiveFailureBudget_le_threshold` is declared in `MIPRE/Foundations/Introspection/AdaptiveIterationBudget.lean`, lines 147–169. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AdaptiveIterationBudget.lean#L147-L169; blueprint lem:intro-iteration-threshold

import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Introspection_ErrorBounds
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveStageBudget
import Definitions.Def_MIPRE_Foundations_Introspection_AdaptiveIterationBudget

open MIPRE
open MIPRE.Introspection

theorem MIPRE.Introspection.adaptiveFailureBudget_le_threshold (r N : ℕ) {edges z h initial : ℝ}
    (hE : 0 ≤ edges) (hi : initial ≤ adaptiveSmallThreshold r edges N)
    (hz : z ≤ adaptiveSmallThreshold r edges N)
    (hh : h ≤ adaptiveSmallThreshold r edges N) :
    ∀ n, n ≤ N → adaptiveFailureBudget r edges z h initial n ≤
      adaptiveSmallThreshold r edges (N - n) := by sorry
