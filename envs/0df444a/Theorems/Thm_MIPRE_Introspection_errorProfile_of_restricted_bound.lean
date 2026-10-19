-- Prove2me | Theorems.Thm_MIPRE_Introspection_errorProfile_of_restricted_bound
-- name    : MIPRE.Introspection.errorProfile_of_restricted_bound
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:10:13.351159+00:00
-- url     : https://prove2.me/theorems/a45af67d-55c5-407c-b680-fd856da64c5e
-- title:
--   A fixed restriction factor and the original-failure budget can both be absorbed into the two-term profile
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.RestrictedErrorBounds` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Absorbing restriction loss into the introspection error profile. Restriction multiplies the QLD failure by a fixed edge count. The finite-game argument also needs a budget for the original failure. These lemmas absorb both changes into constants independent of the verifier index and strategy error.
--
--   A fixed restriction factor and the original-failure budget can both be
--   absorbed into the two-term profile. The large-error case uses only `v ≥ 0`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--
--   theorem MIPRE.Introspection.errorProfile_of_restricted_bound {C a b c x ε δ v : ℝ} (k : ℕ)
--       (hC : 0 ≤ C) (ha : 1 ≤ a) (hb0 : 0 < b) (hb1 : b ≤ 1)
--       (hc : 1 ≤ c) (hx : 1 ≤ x) (hε : 0 ≤ ε)
--       (hδ : δ ≤ errorProfile a b x (c * ε)) (hv : 0 ≤ v)
--       (hvalue : 1 - C * iteratedRoot k (max ε δ) ≤ v) :
--       1 - errorProfile
--         (powerCoefficient (C * (max 1 (c ^ b)) ^ rootExponent k) a (rootExponent k))
--         (b * rootExponent k) x ε ≤ v
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.errorProfile_of_restricted_bound` is declared in `MIPRE/Foundations/Introspection/RestrictedErrorBounds.lean`, lines 49–72. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/RestrictedErrorBounds.lean#L49-L72

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

theorem MIPRE.Introspection.errorProfile_of_restricted_bound {C a b c x ε δ v : ℝ} (k : ℕ)
    (hC : 0 ≤ C) (ha : 1 ≤ a) (hb0 : 0 < b) (hb1 : b ≤ 1)
    (hc : 1 ≤ c) (hx : 1 ≤ x) (hε : 0 ≤ ε)
    (hδ : δ ≤ errorProfile a b x (c * ε)) (hv : 0 ≤ v)
    (hvalue : 1 - C * iteratedRoot k (max ε δ) ≤ v) :
    1 - errorProfile
      (powerCoefficient (C * (max 1 (c ^ b)) ^ rootExponent k) a (rootExponent k))
      (b * rootExponent k) x ε ≤ v := by sorry
