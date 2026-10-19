-- Prove2me | Theorems.Thm_MIPRE_Introspection_errorProfile_scale_input
-- name    : MIPRE.Introspection.errorProfile_scale_input
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:10:01.142395+00:00
-- url     : https://prove2.me/theorems/639ccf0f-d5c8-4add-b6f3-b691827177f5
-- title:
--   Scaling the test error, as happens in detyping, changes only a fixed coefficient
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.ErrorBounds` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Normalizing the final introspection error. The paper's final soundness estimate absorbs any fixed concave power and constant multiple into `a * (x^a * ε^b + x^(-b))`. The coefficient and the new exponent are explicit here, including the normalization `a ≥ 1`, `0 < b ≤ 1`. No induction estimate is assumed or encoded by the definitions in this file.
--
--   Scaling the test error, as happens in detyping, changes only a fixed coefficient.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--
--   theorem MIPRE.Introspection.errorProfile_scale_input {a b c x ε : ℝ}
--       (ha : 0 ≤ a) (hc : 0 ≤ c) (hx : 0 ≤ x) (hε : 0 ≤ ε) :
--       errorProfile a b x (c * ε) ≤ max 1 (c ^ b) * errorProfile a b x ε
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.errorProfile_scale_input` is declared in `MIPRE/Foundations/Introspection/ErrorBounds.lean`, lines 127–142. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/ErrorBounds.lean#L127-L142; blueprint lem:intro-error-absorption

import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Introspection_ErrorBounds

open MIPRE
open MIPRE.Introspection

theorem MIPRE.Introspection.errorProfile_scale_input {a b c x ε : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hx : 0 ≤ x) (hε : 0 ≤ ε) :
    errorProfile a b x (c * ε) ≤ max 1 (c ^ b) * errorProfile a b x ε := by sorry
