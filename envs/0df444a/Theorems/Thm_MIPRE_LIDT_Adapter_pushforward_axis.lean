-- Prove2me | Theorems.Thm_MIPRE_LIDT_Adapter_pushforward_axis
-- name    : MIPRE.LIDT.Adapter.pushforward_axis
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:01:41.661977+00:00
-- url     : https://prove2.me/theorems/f6d2b8c6-1d73-4d92-a0ca-041e630e3d55
-- title:
--   The axis-parallel shape of the push-forward bound. The one contributing sample has weight 1/(6 m q^m), the family pins one seed index, and the seeded test puts at least…
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.Adapter.Weights` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The seeded-CL adapter, part 5: both tests' distributions, as counts. The reduction's remaining obligation is a push-forward bound between the two tests' question distributions, and both are defined as sums over a `Sample` type against an indicator. So the first thing to do is to turn each into a *count*, after which the bound is arithmetic on cardinalities rather than on sums. * `clGame`'s distribution is uniform over its samples, so it is the number of samples producing the question pair, over the total (`clGame_μ_eq`). * `lidtGame`'s is not uniform — its three subtests are weighted `1/3`…
--
--   **The axis-parallel shape of the push-forward bound.** The one contributing sample has weight
--   `1/(6 m q^m)`, the family pins one seed index, and the seeded test puts at least `1/(9 q^{m+1})`
--   on the pair; the three combine with room to spare at `C = 3m` (`3/2` would do).
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
--   theorem MIPRE.LIDT.Adapter.pushforward_axis (hm : m ∣ Fintype.card F) (u₀ : Point F m) (s₀ : F) (yp : Point F m) :
--       (∑ σc : Seed F m,
--           ∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = CL.Question.aline u₀ s₀),
--           ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = CL.Question.point yp),
--             (lidtGame F m d).μ x' y')
--         ≤ (Fintype.card (Seed F m) : ℝ) *
--             (3 * m * (clGame (d := d) (ldc := ldc) hm).μ
--               (CL.Question.aline u₀ s₀) (CL.Question.point yp))
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.Adapter.pushforward_axis` is declared in `MIPRE/Background/LIDT/Adapter/Weights.lean`, lines 952–1057. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Adapter/Weights.lean#L952-L1057

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

theorem MIPRE.LIDT.Adapter.pushforward_axis (hm : m ∣ Fintype.card F) (u₀ : Point F m) (s₀ : F) (yp : Point F m) :
    (∑ σc : Seed F m,
        ∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = CL.Question.aline u₀ s₀),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = CL.Question.point yp),
          (lidtGame F m d).μ x' y')
      ≤ (Fintype.card (Seed F m) : ℝ) *
          (3 * m * (clGame (d := d) (ldc := ldc) hm).μ
            (CL.Question.aline u₀ s₀) (CL.Question.point yp)) := by sorry
