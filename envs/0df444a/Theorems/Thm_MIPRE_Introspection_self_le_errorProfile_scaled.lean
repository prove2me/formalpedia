-- Prove2me | Theorems.Thm_MIPRE_Introspection_self_le_errorProfile_scaled
-- name    : MIPRE.Introspection.self_le_errorProfile_scaled
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:10:02.593184+00:00
-- url     : https://prove2.me/theorems/cd8f3ac9-8a49-4350-8847-629d0d3c1d05
-- title:
--   On the unit interval, the normalized error profile dominates the original failure, even after increasing that failure by a fixed restriction factor
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.RestrictedErrorBounds` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Absorbing restriction loss into the introspection error profile. Restriction multiplies the QLD failure by a fixed edge count. The finite-game argument also needs a budget for the original failure. These lemmas absorb both changes into constants independent of the verifier index and strategy error.
--
--   On the unit interval, the normalized error profile dominates the original
--   failure, even after increasing that failure by a fixed restriction factor.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--
--   theorem MIPRE.Introspection.self_le_errorProfile_scaled {a b c x ε : ℝ}
--       (ha : 1 ≤ a) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hc : 1 ≤ c)
--       (hx : 1 ≤ x) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
--       ε ≤ errorProfile a b x (c * ε)
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.self_le_errorProfile_scaled` is declared in `MIPRE/Foundations/Introspection/RestrictedErrorBounds.lean`, lines 17–35. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/RestrictedErrorBounds.lean#L17-L35

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

theorem MIPRE.Introspection.self_le_errorProfile_scaled {a b c x ε : ℝ}
    (ha : 1 ≤ a) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hc : 1 ≤ c)
    (hx : 1 ≤ x) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ε ≤ errorProfile a b x (c * ε) := by sorry
