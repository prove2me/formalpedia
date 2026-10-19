-- Prove2me | Theorems.Thm_MIPRE_LIDT_CL_Regs_eval_pres
-- name    : MIPRE.LIDT.CL.Regs.eval_pres
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:12:00.628957+00:00
-- url     : https://prove2.me/theorems/5880eb8c-dcd0-4303-8a01-88f2b96d08ee
-- title:
--   Lemma eval_pres of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.PresentationQueries` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The queries of the three-level presentation of the seeded test. What a sampler program must compute for `Regs.pres` (`MIPRE/Background/LIDT/Presentation`), level by level: its marginals (`eval_truncate_one`, `eval_truncate_two`, `eval_pres`), its stage maps read off a prefix (`mapOfPrefix_zero`, `mapOfPrefix_one`, `mapOfPrefix_two`) and its factor spaces (`factorOfPrefix_zero`, `factorOfPrefix_one`, `factorOfPrefix_two`); from the fourth level on there is nothing (`mapOfPrefix_three_le`, `factorOfPrefix_three_le`). The seed a stage map reads is the prefix's seed coordinate, and the diagonal…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LIDT
--   open MIPRE.LIDT.CL
--   open MIPRE.LIDT.CL.Regs
--   open Finset MIPRE.CL MIPRE.CL.CLFun
--   variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
--
--   theorem MIPRE.LIDT.CL.Regs.eval_pres (t : Ty) (x : ι → F) :
--       (R.pres S t).eval x = R.seedLin t x + R.secondLin S t (x R.coord) x +
--         R.putPt (ptMap S t (x R.coord)
--           (if t = .dline then zeroBelow (S.χ (x R.coord)) (R.dirOf x) else 0) (R.ptOf x))
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.CL.Regs.eval_pres` is declared in `MIPRE/Background/LIDT/PresentationQueries.lean`, lines 96–116. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/PresentationQueries.lean#L96-L116; blueprint lem:ar-typed-sampler

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.Defs
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
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Background_LIDT_Presentation
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Product
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_CL_ProductSampler
import Definitions.Def_MIPRE_Background_LIDT_PresentationQueries

open MIPRE
open MIPRE.LIDT
open MIPRE.LIDT.CL
open MIPRE.LIDT.CL.Regs
open Finset MIPRE.CL MIPRE.CL.CLFun
variable {ι : Type*} [DecidableEq ι] [Fintype ι] {n : ℕ} (R : Regs ι n)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [NeZero n] {hn : n ∣ Fintype.card F}
  (S : Sel F n hn)

theorem MIPRE.LIDT.CL.Regs.eval_pres (t : Ty) (x : ι → F) :
    (R.pres S t).eval x = R.seedLin t x + R.secondLin S t (x R.coord) x +
      R.putPt (ptMap S t (x R.coord)
        (if t = .dline then zeroBelow (S.χ (x R.coord)) (R.dirOf x) else 0) (R.ptOf x)) := by sorry
