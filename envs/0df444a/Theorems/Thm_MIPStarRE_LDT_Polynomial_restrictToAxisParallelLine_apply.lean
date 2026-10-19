-- Prove2me | Theorems.Thm_MIPStarRE_LDT_Polynomial_restrictToAxisParallelLine_apply
-- name    : MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine_apply
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:04:08.017701+00:00
-- url     : https://prove2.me/theorems/ff070688-1bb5-4f8c-92e8-06dcb02f0806
-- title:
--   Evaluating an axis-parallel restriction agrees with evaluating the original polynomial at the corresponding point on the line
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Basic.LowDegreePolynomial` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Low-individual-degree polynomials for the low individual degree test. Multivariate low-degree polynomial objects and their restrictions. Note: this module contributes declarations to the comparator statement closure of `mainFormal`, which must elaborate in the same environment as the Mathlib-only `Challenge.lean`. Keep the full `import Mathlib`; do not narrow it. See `docs/comparator.md`, "Environment alignment".
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   Evaluating an axis-parallel restriction agrees with evaluating the original
--   polynomial at the corresponding point on the line.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPStarRE
--   open MIPStarRE.LDT
--   open MIPStarRE.LDT.Polynomial
--
--   theorem MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine_apply
--       (params : Parameters) [FieldModel params.q]
--       (g : Polynomial params) (ℓ : AxisParallelLine params) (t : Fq params) :
--       restrictToAxisParallelLine params g ℓ t = g (ℓ.pointAt t)
--   ```
--
--   **Formalization Note** `MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine_apply` is declared in `MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/LowDegreePolynomial.lean`, lines 438–472. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Basic/LowDegreePolynomial.lean#L438-L472

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Multiset.Count
import Mathlib.Data.Multiset.Defs
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.SetLike.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Logic.Nontrivial.Defs
import Mathlib.Logic.Unique
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Nat
import Mathlib.Order.RelClasses
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial

open MIPStarRE
open MIPStarRE.LDT
open MIPStarRE.LDT.Polynomial
set_option backward.isDefEq.respectTransparency false

theorem MIPStarRE.LDT.Polynomial.restrictToAxisParallelLine_apply
    (params : Parameters) [FieldModel params.q]
    (g : Polynomial params) (ℓ : AxisParallelLine params) (t : Fq params) :
    restrictToAxisParallelLine params g ℓ t = g (ℓ.pointAt t) := by sorry
