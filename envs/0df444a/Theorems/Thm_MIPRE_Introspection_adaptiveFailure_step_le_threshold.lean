-- Prove2me | Theorems.Thm_MIPRE_Introspection_adaptiveFailure_step_le_threshold
-- name    : MIPRE.Introspection.adaptiveFailure_step_le_threshold
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:57:05.816116+00:00
-- url     : https://prove2.me/theorems/5a5754ed-6eaa-4f33-9a17-586fd8928cee
-- title:
--   One actual numerical recurrence step consumes exactly one inverse threshold level
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.AdaptiveIterationBudget` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). A positive small-error threshold for every adaptive stage. The failure recurrence has an explicit inverse threshold. For any fixed depth and number of replacements, sufficiently small initial and primitive errors keep every common stage budget at most one. The construction uses the proved triple-square-root replacement loss; no stage-smallness premise is built into the threshold.
--
--   One actual numerical recurrence step consumes exactly one inverse
--   threshold level. In particular, this is derived from the replacement loss
--   formula, rather than requiring the desired next bound as a hypothesis.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--
--   theorem MIPRE.Introspection.adaptiveFailure_step_le_threshold (r n : ℕ) {edges f z h : ℝ}
--       (hE : 0 ≤ edges)
--       (hf : f ≤ adaptiveSmallThreshold r edges (n + 1))
--       (hz : z ≤ adaptiveSmallThreshold r edges (n + 1))
--       (hh : h ≤ adaptiveSmallThreshold r edges (n + 1)) :
--       f + adaptiveStepLoss (adaptiveStageBudget r (edges * f) z h) ≤
--         adaptiveSmallThreshold r edges n
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.adaptiveFailure_step_le_threshold` is declared in `MIPRE/Foundations/Introspection/AdaptiveIterationBudget.lean`, lines 120–145. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AdaptiveIterationBudget.lean#L120-L145

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

theorem MIPRE.Introspection.adaptiveFailure_step_le_threshold (r n : ℕ) {edges f z h : ℝ}
    (hE : 0 ≤ edges)
    (hf : f ≤ adaptiveSmallThreshold r edges (n + 1))
    (hz : z ≤ adaptiveSmallThreshold r edges (n + 1))
    (hh : h ≤ adaptiveSmallThreshold r edges (n + 1)) :
    f + adaptiveStepLoss (adaptiveStageBudget r (edges * f) z h) ≤
      adaptiveSmallThreshold r edges n := by sorry
