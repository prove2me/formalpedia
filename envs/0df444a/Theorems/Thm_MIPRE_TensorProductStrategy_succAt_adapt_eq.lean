-- Prove2me | Theorems.Thm_MIPRE_TensorProductStrategy_succAt_adapt_eq
-- name    : MIPRE.TensorProductStrategy.succAt_adapt_eq
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:22:00.741743+00:00
-- url     : https://prove2.me/theorems/3191ca0a-a961-470a-bfaa-9241b305abe7
-- title:
--   The adapted conditional success probability, as a sum over G's answers: the coarse-graining disappears into the decision predicate
-- statement:
--   A statement of the module `MIPRE.Foundations.GameAdapt` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Playing a strategy for one game as a strategy for another. `MIPRE.Foundations.GameTransport` compares games that share their question alphabets and their distribution. This file drops both assumptions, which is what a *reduction* between two genuinely different games needs: given a strategy `S` for `G`, a map `qA` of the target game's questions into `G`'s and a coarse-graining `rA` of `G`'s answers into the target's, `S.adapt` plays `S` through them.
--
--   The adapted conditional success probability, as a sum over `G`'s answers: the
--   coarse-graining disappears into the decision predicate.
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
--   theorem MIPRE.TensorProductStrategy.succAt_adapt_eq (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
--       (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B') (x' : X') (y' : Y') :
--       (S.adapt G' qA qB rA rB).succAt x' y'
--         = ∑ a, ∑ b, (if G'.D x' y' (rA x' a) (rB y' b) then 1 else 0)
--             * S.born (qA x') (qB y') a b
--   ```
--
--   **Formalization Note** `MIPRE.TensorProductStrategy.succAt_adapt_eq` is declared in `MIPRE/Foundations/GameAdapt.lean`, lines 241–258. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/GameAdapt.lean#L241-L258

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

theorem MIPRE.TensorProductStrategy.succAt_adapt_eq (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B') (x' : X') (y' : Y') :
    (S.adapt G' qA qB rA rB).succAt x' y'
      = ∑ a, ∑ b, (if G'.D x' y' (rA x' a) (rB y' b) then 1 else 0)
          * S.born (qA x') (qB y') a b := by sorry
