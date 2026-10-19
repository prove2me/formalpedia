-- Prove2me | Theorems.Thm_MIPRE_TensorProductStrategy_born_adapt
-- name    : MIPRE.TensorProductStrategy.born_adapt
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:21:58.005159+00:00
-- url     : https://prove2.me/theorems/6ba947aa-af58-43bf-97b5-44f690cc2a5e
-- title:
--   The adapted Born-rule probability is the sum over the fibres of the coarse-graining
-- statement:
--   A statement of the module `MIPRE.Foundations.GameAdapt` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Playing a strategy for one game as a strategy for another. `MIPRE.Foundations.GameTransport` compares games that share their question alphabets and their distribution. This file drops both assumptions, which is what a *reduction* between two genuinely different games needs: given a strategy `S` for `G`, a map `qA` of the target game's questions into `G`'s and a coarse-graining `rA` of `G`'s answers into the target's, `S.adapt` plays `S` through them.
--
--   The adapted Born-rule probability is the sum over the fibres of the coarse-graining.
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
--   variable [DecidableEq A'] [DecidableEq B']
--
--   theorem MIPRE.TensorProductStrategy.born_adapt (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
--       (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B') (x' : X') (y' : Y')
--       (a' : A') (b' : B') :
--       (S.adapt G' qA qB rA rB).born x' y' a' b'
--         = ∑ a ∈ Finset.univ.filter (fun a => rA x' a = a'),
--             ∑ b ∈ Finset.univ.filter (fun b => rB y' b = b'), S.born (qA x') (qB y') a b
--   ```
--
--   **Formalization Note** `MIPRE.TensorProductStrategy.born_adapt` is declared in `MIPRE/Foundations/GameAdapt.lean`, lines 220–239. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/GameAdapt.lean#L220-L239

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
variable [DecidableEq A'] [DecidableEq B']

theorem MIPRE.TensorProductStrategy.born_adapt (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B') (x' : X') (y' : Y')
    (a' : A') (b' : B') :
    (S.adapt G' qA qB rA rB).born x' y' a' b'
      = ∑ a ∈ Finset.univ.filter (fun a => rA x' a = a'),
          ∑ b ∈ Finset.univ.filter (fun b => rB y' b = b'), S.born (qA x') (qB y') a b := by sorry
