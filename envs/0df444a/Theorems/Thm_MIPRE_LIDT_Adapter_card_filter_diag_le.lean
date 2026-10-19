-- Prove2me | Theorems.Thm_MIPRE_LIDT_Adapter_card_filter_diag_le
-- name    : MIPRE.LIDT.Adapter.card_filter_diag_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:00:31.183954+00:00
-- url     : https://prove2.me/theorems/050627bb-dcb6-43e3-92c1-accb25ea5ef1
-- title:
--   At most m q samples produce a given diagonal line against a given point. A sample is pinned by its j together with the scalar relating its direction to the line's, and…
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.Adapter.Weights` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The seeded-CL adapter, part 5: both tests' distributions, as counts. The reduction's remaining obligation is a push-forward bound between the two tests' question distributions, and both are defined as sums over a `Sample` type against an indicator. So the first thing to do is to turn each into a *count*, after which the bound is arithmetic on cardinalities rather than on sums. * `clGame`'s distribution is uniform over its samples, so it is the number of samples producing the question pair, over the total (`clGame_μ_eq`). * `lidtGame`'s is not uniform — its three subtests are weighted `1/3`…
--
--   **At most `m q` samples produce a given diagonal line against a given point.** A sample is
--   pinned by its `j` together with the scalar relating its direction to the line's, and there are
--   `m` values of the first and `q` of the second.
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
--   theorem MIPRE.LIDT.Adapter.card_filter_diag_le {ℓ : Line F m} (hℓ : ∃ k, ℓ.2 k ≠ 0) (u : Point F m) :
--       (Finset.univ.filter (fun s : Sample F m =>
--           s.questions = ((Question.diagLine ℓ : Question F m), Question.point u))).card
--         ≤ m * Fintype.card F
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.Adapter.card_filter_diag_le` is declared in `MIPRE/Background/LIDT/Adapter/Weights.lean`, lines 251–287. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Adapter/Weights.lean#L251-L287

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

theorem MIPRE.LIDT.Adapter.card_filter_diag_le {ℓ : Line F m} (hℓ : ∃ k, ℓ.2 k ≠ 0) (u : Point F m) :
    (Finset.univ.filter (fun s : Sample F m =>
        s.questions = ((Question.diagLine ℓ : Question F m), Question.point u))).card
      ≤ m * Fintype.card F := by sorry
