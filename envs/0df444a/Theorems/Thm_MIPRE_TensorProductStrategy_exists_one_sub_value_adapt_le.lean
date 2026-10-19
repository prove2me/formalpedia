-- Prove2me | Theorems.Thm_MIPRE_TensorProductStrategy_exists_one_sub_value_adapt_le
-- name    : MIPRE.TensorProductStrategy.exists_one_sub_value_adapt_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:22:00.799955+00:00
-- url     : https://prove2.me/theorems/b0c66969-9ec5-467a-b2ef-77d0e59a7e17
-- title:
--   The averaged form of one_sub_value_adapt_le. The push-forward bound need only hold on average over a finite family of question maps; some member of the family then achieves…
-- statement:
--   A statement of the module `MIPRE.Foundations.GameAdapt` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Playing a strategy for one game as a strategy for another. `MIPRE.Foundations.GameTransport` compares games that share their question alphabets and their distribution. This file drops both assumptions, which is what a *reduction* between two genuinely different games needs: given a strategy `S` for `G`, a map `qA` of the target game's questions into `G`'s and a coarse-graining `rA` of `G`'s answers into the target's, `S.adapt` plays `S` through them.
--
--   **The averaged form of `one_sub_value_adapt_le`.** The push-forward bound need only hold on
--   average over a finite family of question maps; some member of the family then achieves the
--   conclusion. This is how a reduction that must *choose* a preimage of each target question pays
--   back the size of the fibre.
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
--   theorem MIPRE.TensorProductStrategy.exists_one_sub_value_adapt_le {Seed : Type*} [Fintype Seed] [Nonempty Seed]
--       (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
--       (qA : Seed → X' → X) (qB : Seed → Y' → Y) (rA : Seed → X' → A → A')
--       (rB : Seed → Y' → B → B') (C : ℝ)
--       (hD : ∀ σ x' y' a b, G'.μ x' y' ≠ 0 →
--         G.D (qA σ x') (qB σ y') a b = true → G'.D x' y' (rA σ x' a) (rB σ y' b) = true)
--       (hμ : ∀ x y, (∑ σ, ∑ x' ∈ Finset.univ.filter (fun x' => qA σ x' = x),
--           ∑ y' ∈ Finset.univ.filter (fun y' => qB σ y' = y), G'.μ x' y')
--         ≤ (Fintype.card Seed : ℝ) * (C * G.μ x y)) :
--       ∃ σ : Seed,
--         1 - (S.adapt G' (qA σ) (qB σ) (rA σ) (rB σ)).value ≤ C * (1 - S.value)
--   ```
--
--   **Formalization Note** `MIPRE.TensorProductStrategy.exists_one_sub_value_adapt_le` is declared in `MIPRE/Foundations/GameAdapt.lean`, lines 336–377. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/GameAdapt.lean#L336-L377

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

theorem MIPRE.TensorProductStrategy.exists_one_sub_value_adapt_le {Seed : Type*} [Fintype Seed] [Nonempty Seed]
    (S : TensorProductStrategy G) (G' : Game X' Y' A' B')
    (qA : Seed → X' → X) (qB : Seed → Y' → Y) (rA : Seed → X' → A → A')
    (rB : Seed → Y' → B → B') (C : ℝ)
    (hD : ∀ σ x' y' a b, G'.μ x' y' ≠ 0 →
      G.D (qA σ x') (qB σ y') a b = true → G'.D x' y' (rA σ x' a) (rB σ y' b) = true)
    (hμ : ∀ x y, (∑ σ, ∑ x' ∈ Finset.univ.filter (fun x' => qA σ x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => qB σ y' = y), G'.μ x' y')
      ≤ (Fintype.card Seed : ℝ) * (C * G.μ x y)) :
    ∃ σ : Seed,
      1 - (S.adapt G' (qA σ) (qB σ) (rA σ) (rB σ)).value ≤ C * (1 - S.value) := by sorry
