-- Prove2me | Theorems.Thm_MIPRE_LIDT_Adapter_pushforward_diag_ne
-- name    : MIPRE.LIDT.Adapter.pushforward_diag_ne
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:02:42.677153+00:00
-- url     : https://prove2.me/theorems/f08b67a1-4418-401a-940d-00d7d2c7824d
-- title:
--   The nondegenerate diagonal shape of the push-forward bound. At most m q samples contribute, each of weight at most 1/(6 m q^m q^{J+1}), and the family is pinned both at…
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.Adapter.Weights` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The seeded-CL adapter, part 5: both tests' distributions, as counts. The reduction's remaining obligation is a push-forward bound between the two tests' question distributions, and both are defined as sums over a `Sample` type against an indicator. So the first thing to do is to turn each into a *count*, after which the bound is arithmetic on cardinalities rather than on sums. * `clGame`'s distribution is uniform over its samples, so it is the number of samples producing the question pair, over the total (`clGame_μ_eq`). * `lidtGame`'s is not uniform — its three subtests are weighted `1/3`…
--
--   **The nondegenerate diagonal shape of the push-forward bound.** At most `m q` samples
--   contribute, each of weight at most `1/(6 m q^m q^{J+1})`, and the family is pinned both at the
--   seed index and on the scale, so only `(q/m)^{m-1}` of its members can contribute. Against the
--   seeded test's `q^{χ}` samples, with `J + 1 + χ = m`, the constant comes out `3q/(2(q-1))`, which
--   `C = 3m` covers for every `q ≥ 2`.
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
--   theorem MIPRE.LIDT.Adapter.pushforward_diag_ne (hm : m ∣ Fintype.card F) (u₀ : Point F m) (s₀ : F) {w : Point F m}
--       (hw : w ≠ 0) (yp : Point F m) :
--       (∑ σc : Seed F m,
--           ∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = CL.Question.dline u₀ s₀ w),
--           ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = CL.Question.point yp),
--             (lidtGame F m d).μ x' y')
--         ≤ (Fintype.card (Seed F m) : ℝ) *
--             (3 * m * (clGame (d := d) (ldc := ldc) hm).μ
--               (CL.Question.dline u₀ s₀ w) (CL.Question.point yp))
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.Adapter.pushforward_diag_ne` is declared in `MIPRE/Background/LIDT/Adapter/Weights.lean`, lines 1590–1754. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Adapter/Weights.lean#L1590-L1754

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

theorem MIPRE.LIDT.Adapter.pushforward_diag_ne (hm : m ∣ Fintype.card F) (u₀ : Point F m) (s₀ : F) {w : Point F m}
    (hw : w ≠ 0) (yp : Point F m) :
    (∑ σc : Seed F m,
        ∑ x' ∈ Finset.univ.filter (fun x' => qmapS hm σc x' = CL.Question.dline u₀ s₀ w),
        ∑ y' ∈ Finset.univ.filter (fun y' => qmapS hm σc y' = CL.Question.point yp),
          (lidtGame F m d).μ x' y')
      ≤ (Fintype.card (Seed F m) : ℝ) *
          (3 * m * (clGame (d := d) (ldc := ldc) hm).μ
            (CL.Question.dline u₀ s₀ w) (CL.Question.point yp)) := by sorry
