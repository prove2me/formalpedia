-- Prove2me | Theorems.Thm_MIPRE_Introspection_one_le_soundness_power_of_threshold_le
-- name    : MIPRE.Introspection.one_le_soundness_power_of_threshold_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:09:23.331186+00:00
-- url     : https://prove2.me/theorems/2bf0bcca-bcc9-45d8-8905-7c56cd510bd1
-- title:
--   If the common input error exceeds the explicit admissible threshold, the same soundness power bound is at least one
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.AdaptivePowerBudget` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Power bounds for the full finite adaptive recurrence. Each replacement introduces three square roots. For any fixed number of replacements the actual failure recurrence is bounded by an explicit constant times the corresponding iterated root of a common primitive error. A second explicit coefficient makes this bound at least one outside the proved admissible small-error regime. These numerical statements do not assume the existence or soundness of the strategy construction.
--
--   If the common input error exceeds the explicit admissible threshold,
--   the same soundness power bound is at least one.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--
--   theorem MIPRE.Introspection.one_le_soundness_power_of_threshold_le (r n : ℕ) {edges t : ℝ}
--       (hE : 0 ≤ edges) (ht : adaptiveSmallThreshold r edges n ≤ t) :
--       1 ≤ adaptiveSoundnessCoefficient r edges n * iteratedRoot (3 * n) t
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.one_le_soundness_power_of_threshold_le` is declared in `MIPRE/Foundations/Introspection/AdaptivePowerBudget.lean`, lines 196–212. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/AdaptivePowerBudget.lean#L196-L212

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

theorem MIPRE.Introspection.one_le_soundness_power_of_threshold_le (r n : ℕ) {edges t : ℝ}
    (hE : 0 ≤ edges) (ht : adaptiveSmallThreshold r edges n ≤ t) :
    1 ≤ adaptiveSoundnessCoefficient r edges n * iteratedRoot (3 * n) t := by sorry
