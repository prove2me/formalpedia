-- Prove2me | Theorems.Thm_MIPStarRE_LDT_embedCoord_ne_lastCoord
-- name    : MIPStarRE.LDT.embedCoord_ne_lastCoord
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:15:20.726908+00:00
-- url     : https://prove2.me/theorems/f449d525-b56c-4218-9132-6eaae7864a9a
-- title:
--   No old coordinate is the appended last coordinate
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.ParametersBase` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Basic parameters and scalar infrastructure for the low individual degree test. Core parameter data, finite-field models, and coordinate arithmetic. Note: this module contributes declarations to the comparator statement closure of `mainFormal`, which must elaborate in the same environment as the Mathlib-only `Challenge.lean`. Keep the full `import Mathlib`; do not narrow it. See `docs/comparator.md`, "Environment alignment".
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   No old coordinate is the appended last coordinate.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPStarRE
--   open MIPStarRE.LDT
--   open scoped BigOperators MatrixOrder Matrix ComplexOrder
--
--   theorem MIPStarRE.LDT.embedCoord_ne_lastCoord (params : Parameters) (i : Fin params.m) :
--       embedCoord params i ≠ lastCoord params
--   ```
--
--   **Formalization Note** `MIPStarRE.LDT.embedCoord_ne_lastCoord` is declared in `MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/ParametersBase.lean`, lines 428–434. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/ParametersBase.lean#L428-L434

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

open MIPStarRE
open MIPStarRE.LDT
open scoped BigOperators MatrixOrder Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
attribute [instance] MIPStarRE.LDT.FieldModel.instField MIPStarRE.LDT.FieldModel.instFintype MIPStarRE.LDT.FieldModel.instDecidableEq

theorem MIPStarRE.LDT.embedCoord_ne_lastCoord (params : Parameters) (i : Fin params.m) :
    embedCoord params i ≠ lastCoord params := by sorry
