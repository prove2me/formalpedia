-- Prove2me | Theorems.Thm_MIPStarRE_LDT_AxisParallelLine_appendAtHeight_rebaseAt
-- name    : MIPStarRE.LDT.AxisParallelLine.appendAtHeight_rebaseAt
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:11:09.787975+00:00
-- url     : https://prove2.me/theorems/d6a9c517-78d4-44ae-8609-617d36542484
-- title:
--   Lemma appendAtHeight_rebaseAt of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.AxisParallelLine` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Axis-parallel lines for the low individual degree test. Axis-parallel line geometry on top of the core parameter infrastructure: `AxisParallelLine` records a base point and a coordinate direction, with canonical parameterization, rebasing, and slice-embedding operations.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPStarRE
--   open MIPStarRE.LDT
--   open MIPStarRE.LDT.AxisParallelLine
--
--   theorem MIPStarRE.LDT.AxisParallelLine.appendAtHeight_rebaseAt {params : Parameters} [FieldModel params.q]
--       (ℓ : AxisParallelLine params) (t x : Fq params) :
--       appendAtHeight params (rebaseAt ℓ t) x =
--         rebaseAt (appendAtHeight params ℓ x) t
--   ```
--
--   **Formalization Note** `MIPStarRE.LDT.AxisParallelLine.appendAtHeight_rebaseAt` is declared in `MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/AxisParallelLine.lean`, lines 129–158. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/AxisParallelLine.lean#L129-L158

import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine

open MIPStarRE
open MIPStarRE.LDT
open MIPStarRE.LDT.AxisParallelLine
set_option backward.isDefEq.respectTransparency false

theorem MIPStarRE.LDT.AxisParallelLine.appendAtHeight_rebaseAt {params : Parameters} [FieldModel params.q]
    (ℓ : AxisParallelLine params) (t x : Fq params) :
    appendAtHeight params (rebaseAt ℓ t) x =
      rebaseAt (appendAtHeight params ℓ x) t := by sorry
