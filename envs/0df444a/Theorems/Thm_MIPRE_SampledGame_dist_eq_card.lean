-- Prove2me | Theorems.Thm_MIPRE_SampledGame_dist_eq_card
-- name    : MIPRE.SampledGame.dist_eq_card
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:28:07.546112+00:00
-- url     : https://prove2.me/theorems/9f225420-d39a-404a-9e28-ae59b4b28049
-- title:
--   The sample law is the normalized cardinality of each question pair's fibre
-- statement:
--   A statement of the module `MIPRE.Foundations.SampledGame` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Games generated from finite uniform samples. Unlike `SeededGame`, the seed and the two question alphabets may differ. This is needed for typed games, whose seed is an edge and a common vector.
--
--   The sample law is the normalized cardinality of each question pair's fibre.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SampledGame
--   open Finset Classical
--   variable {S X Y : Type*} [Fintype S] [Fintype X] [Fintype Y]
--
--   theorem MIPRE.SampledGame.dist_eq_card (qA : S → X) (qB : S → Y) (x : X) (y : Y) :
--       dist qA qB x y = ((univ.filter fun s => qA s = x ∧ qB s = y).card : ℝ) / Fintype.card S
--   ```
--
--   **Formalization Note** `MIPRE.SampledGame.dist_eq_card` is declared in `MIPRE/Foundations/SampledGame.lean`, lines 29–33. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SampledGame.lean#L29-L33

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

theorem MIPRE.SampledGame.dist_eq_card (qA : S → X) (qB : S → Y) (x : X) (y : Y) :
    dist qA qB x y = ((univ.filter fun s => qA s = x ∧ qB s = y).card : ℝ) / Fintype.card S := by sorry
