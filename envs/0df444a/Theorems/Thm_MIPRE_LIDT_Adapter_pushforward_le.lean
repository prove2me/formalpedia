-- Prove2me | Theorems.Thm_MIPRE_LIDT_Adapter_pushforward_le
-- name    : MIPRE.LIDT.Adapter.pushforward_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:03:21.069915+00:00
-- url     : https://prove2.me/theorems/e5db4857-d25d-4e78-9b4b-f673df34c5ab
-- title:
--   The push-forward bound, assembled. The average over the family of the canonical-line test's mass on the fibre of a seeded question pair is at most 3m times the seeded test's…
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.Adapter.Weights` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The seeded-CL adapter, part 5: both tests' distributions, as counts. The reduction's remaining obligation is a push-forward bound between the two tests' question distributions, and both are defined as sums over a `Sample` type against an indicator. So the first thing to do is to turn each into a *count*, after which the bound is arithmetic on cardinalities rather than on sums. * `clGame`'s distribution is uniform over its samples, so it is the number of samples producing the question pair, over the total (`clGame_μ_eq`). * `lidtGame`'s is not uniform — its three subtests are weighted `1/3`…
--
--   **The push-forward bound, assembled.** The average over the family of the canonical-line
--   test's mass on the fibre of a seeded question pair is at most `3m` times the seeded test's mass
--   on it. This is the hypothesis `exists_one_sub_value_adapt_le` asks for, and `3m` is the constant
--   `thm:lidt-cl-soundness` multiplies its `ε` by --- polynomial in `m`, as `δ_CL` allows, and free
--   of `q`, which it does not.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LIDT
--   open MIPRE.LIDT.Adapter
--   open Finset MIPRE.LIDT MIPRE.LIDT.CL
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
--
--   theorem MIPRE.LIDT.Adapter.pushforward_le (hm : m ∣ Fintype.card F) (x y : CL.Question F m) :
--       (∑ σc : Seed F m, ∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = x),
--           ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = y), (lidtGame F m d).μ x' y')
--         ≤ (Fintype.card (Seed F m) : ℝ) *
--             (3 * m * (clGame (d := d) (ldc := ldc) hm).μ x y)
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.Adapter.pushforward_le` is declared in `MIPRE/Background/LIDT/Adapter/Weights.lean`, lines 1826–1857. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Adapter/Weights.lean#L1826-L1857; blueprint lem:lidt-cl-adapter-weights

import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Weights

open MIPRE
open MIPRE.LIDT
open MIPRE.LIDT.Adapter
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]

theorem MIPRE.LIDT.Adapter.pushforward_le (hm : m ∣ Fintype.card F) (x y : CL.Question F m) :
    (∑ σc : Seed F m, ∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = x),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = y), (lidtGame F m d).μ x' y')
      ≤ (Fintype.card (Seed F m) : ℝ) *
          (3 * m * (clGame (d := d) (ldc := ldc) hm).μ x y) := by sorry
