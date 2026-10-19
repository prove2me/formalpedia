-- Prove2me | Theorems.Thm_MIPRE_SampledGame_one_sub_value
-- name    : MIPRE.SampledGame.one_sub_value
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:28:49.901764+00:00
-- url     : https://prove2.me/theorems/dfb60c85-3156-468a-b23a-b76d68eee013
-- title:
--   The failure probability of a strategy is the uniform average of its conditional failures
-- statement:
--   A statement of the module `MIPRE.Foundations.SampledGame` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Games generated from finite uniform samples. Unlike `SeededGame`, the seed and the two question alphabets may differ. This is needed for typed games, whose seed is an edge and a common vector.
--
--   The failure probability of a strategy is the uniform average of its conditional failures.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SampledGame
--   open Finset Classical
--   variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]
--
--   theorem MIPRE.SampledGame.one_sub_value [Nonempty S] {A B : Type*} [Fintype A] [Fintype B]
--       (qA : S → X) (qB : S → Y) (D : X → Y → A → B → Bool)
--       (R : TensorProductStrategy (game qA qB D)) :
--       1 - R.value = (∑ s, R.failAt (qA s) (qB s)) / Fintype.card S
--   ```
--
--   **Formalization Note** `MIPRE.SampledGame.one_sub_value` is declared in `MIPRE/Foundations/SampledGame.lean`, lines 71–77. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SampledGame.lean#L71-L77; blueprint lem:detype-game-soundness

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_SampledGame

open MIPRE
open MIPRE.SampledGame
open Finset Classical
set_option linter.unusedSectionVars false
variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]

theorem MIPRE.SampledGame.one_sub_value [Nonempty S] {A B : Type*} [Fintype A] [Fintype B]
    (qA : S → X) (qB : S → Y) (D : X → Y → A → B → Bool)
    (R : TensorProductStrategy (game qA qB D)) :
    1 - R.value = (∑ s, R.failAt (qA s) (qB s)) / Fintype.card S := by sorry
