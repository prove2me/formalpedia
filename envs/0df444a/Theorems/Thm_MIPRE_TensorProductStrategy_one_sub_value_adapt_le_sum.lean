-- Prove2me | Theorems.Thm_MIPRE_TensorProductStrategy_one_sub_value_adapt_le_sum
-- name    : MIPRE.TensorProductStrategy.one_sub_value_adapt_le_sum
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:22:04.820447+00:00
-- url     : https://prove2.me/theorems/1a361430-0b32-487b-9e8b-c968b2b81ca1
-- title:
--   The failure of the adapted strategy, bounded by G's failure weighted by the push-forward of G''s distribution
-- statement:
--   A statement of the module `MIPRE.Foundations.GameAdapt` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Playing a strategy for one game as a strategy for another. `MIPRE.Foundations.GameTransport` compares games that share their question alphabets and their distribution. This file drops both assumptions, which is what a *reduction* between two genuinely different games needs: given a strategy `S` for `G`, a map `qA` of the target game's questions into `G`'s and a coarse-graining `rA` of `G`'s answers into the target's, `S.adapt` plays `S` through them.
--
--   The failure of the adapted strategy, bounded by `G`'s failure weighted by the push-forward
--   of `G'`'s distribution.
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
--   variable [DecidableEq X] [DecidableEq Y]
--
--   theorem MIPRE.TensorProductStrategy.one_sub_value_adapt_le_sum (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
--       (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B')
--       (hD : ∀ x' y' a b, G'.μ x' y' ≠ 0 →
--         G.D (qA x') (qB y') a b = true → G'.D x' y' (rA x' a) (rB y' b) = true) :
--       1 - (S.adapt G' qA qB rA rB).value
--         ≤ ∑ x, ∑ y, (∑ x' ∈ Finset.univ.filter (fun x' => qA x' = x),
--             ∑ y' ∈ Finset.univ.filter (fun y' => qB y' = y), G'.μ x' y') * S.failAt x y
--   ```
--
--   **Formalization Note** `MIPRE.TensorProductStrategy.one_sub_value_adapt_le_sum` is declared in `MIPRE/Foundations/GameAdapt.lean`, lines 288–314. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/GameAdapt.lean#L288-L314

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
variable [DecidableEq X] [DecidableEq Y]

theorem MIPRE.TensorProductStrategy.one_sub_value_adapt_le_sum (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : X' → X) (qB : Y' → Y) (rA : X' → A → A') (rB : Y' → B → B')
    (hD : ∀ x' y' a b, G'.μ x' y' ≠ 0 →
      G.D (qA x') (qB y') a b = true → G'.D x' y' (rA x' a) (rB y' b) = true) :
    1 - (S.adapt G' qA qB rA rB).value
      ≤ ∑ x, ∑ y, (∑ x' ∈ Finset.univ.filter (fun x' => qA x' = x),
          ∑ y' ∈ Finset.univ.filter (fun y' => qB y' = y), G'.μ x' y') * S.failAt x y := by sorry
