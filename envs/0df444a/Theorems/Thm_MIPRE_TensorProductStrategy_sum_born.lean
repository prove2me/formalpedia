-- Prove2me | Theorems.Thm_MIPRE_TensorProductStrategy_sum_born
-- name    : MIPRE.TensorProductStrategy.sum_born
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:21:50.942839+00:00
-- url     : https://prove2.me/theorems/09bdf5b4-477b-4bb5-a53d-f2e50d176feb
-- title:
--   Lemma sum_born of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.GameAdapt` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Playing a strategy for one game as a strategy for another. `MIPRE.Foundations.GameTransport` compares games that share their question alphabets and their distribution. This file drops both assumptions, which is what a *reduction* between two genuinely different games needs: given a strategy `S` for `G`, a map `qA` of the target game's questions into `G`'s and a coarse-graining `rA` of `G`'s answers into the target's, `S.adapt` plays `S` through them.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.TensorProductStrategy
--   open Matrix Kronecker Finset
--   variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
--   variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
--   variable {G : Game X Y A B}
--
--   theorem MIPRE.TensorProductStrategy.sum_born (S : TensorProductStrategy G) (x : X) (y : Y) :
--       ∑ a, ∑ b, S.born x y a b = 1
--   ```
--
--   **Formalization Note** `MIPRE.TensorProductStrategy.sum_born` is declared in `MIPRE/Foundations/GameAdapt.lean`, lines 153–155. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/GameAdapt.lean#L153-L155

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt

open MIPRE
open MIPRE.TensorProductStrategy
open Matrix Kronecker Finset
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {X' Y' A' B' : Type*} [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']
variable {G : Game X Y A B}

theorem MIPRE.TensorProductStrategy.sum_born (S : TensorProductStrategy G) (x : X) (y : Y) :
    ∑ a, ∑ b, S.born x y a b = 1 := by sorry
