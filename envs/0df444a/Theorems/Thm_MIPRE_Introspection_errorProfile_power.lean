-- Prove2me | Theorems.Thm_MIPRE_Introspection_errorProfile_power
-- name    : MIPRE.Introspection.errorProfile_power
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:09:58.975583+00:00
-- url     : https://prove2.me/theorems/e5d8c4cb-a8e7-496f-a1fa-fca0f72bf3d3
-- title:
--   A fixed concave power of the original soundness profile has the required final shape
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.ErrorBounds` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Normalizing the final introspection error. The paper's final soundness estimate absorbs any fixed concave power and constant multiple into `a * (x^a * ε^b + x^(-b))`. The coefficient and the new exponent are explicit here, including the normalization `a ≥ 1`, `0 < b ≤ 1`. No induction estimate is assumed or encoded by the definitions in this file.
--
--   A fixed concave power of the original soundness profile has the required final shape.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--
--   theorem MIPRE.Introspection.errorProfile_power {C a b r x ε : ℝ}
--       (hC : 0 ≤ C) (ha : 0 ≤ a) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
--       (hx : 1 ≤ x) (hε : 0 ≤ ε) :
--       C * (errorProfile a b x ε) ^ r ≤
--         errorProfile (powerCoefficient C a r) (b * r) x ε
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.errorProfile_power` is declared in `MIPRE/Foundations/Introspection/ErrorBounds.lean`, lines 40–69. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/ErrorBounds.lean#L40-L69; blueprint lem:intro-error-absorption

import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Introspection_ErrorBounds

open MIPRE
open MIPRE.Introspection

theorem MIPRE.Introspection.errorProfile_power {C a b r x ε : ℝ}
    (hC : 0 ≤ C) (ha : 0 ≤ a) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hx : 1 ≤ x) (hε : 0 ≤ ε) :
    C * (errorProfile a b x ε) ^ r ≤
      errorProfile (powerCoefficient C a r) (b * r) x ε := by sorry
