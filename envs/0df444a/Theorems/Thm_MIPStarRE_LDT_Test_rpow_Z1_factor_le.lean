-- Prove2me | Theorems.Thm_MIPStarRE_LDT_Test_rpow_Z1_factor_le
-- name    : MIPStarRE.LDT.Test.rpow_Z1_factor_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:17:43.360975+00:00
-- url     : https://prove2.me/theorems/e0ea7458-2596-4298-9f0f-29dc5dbb3f9c
-- title:
--   Lemma rpow_Z1_factor_le of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Test.MainTheorem.ScalarBounds.EnvelopeBounds` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Error cascade — envelope and root bounding machinery. Internal helper lemmas for the error-cascade bookkeeping of Step 8. These provide the step-envelope interpolation (`stepEnvelope`), monotonicity under denominator enlargement, square-root scaling, and explicit numeric bounds on various `rpow` and `sqrt` expressions. All lemmas are technical and should not be part of downstream API.
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPStarRE
--   open MIPStarRE.LDT
--   open MIPStarRE.LDT.Test
--   open scoped BigOperators
--
--   theorem MIPStarRE.LDT.Test.rpow_Z1_factor_le {params : Parameters} {k : ℕ}
--       {Z1 k2 m4 E2048 r Crpow Erpow : Error}
--       (hZ1NN : 0 ≤ Z1)
--       (hZ1 : Z1 ≤ 20204 * k2 * m4 * E2048)
--       (hrNN : 0 ≤ r)
--       (hk2NN : 0 ≤ k2)
--       (hm4NN : 0 ≤ m4)
--       (hE2048NN : 0 ≤ E2048)
--       (hA : Real.rpow (20204 : Error) r ≤ Crpow)
--       (hB : Real.rpow k2 r ≤ (k : Error))
--       (hC : Real.rpow m4 r ≤ (params.m : Error))
--       (hD : Real.rpow E2048 r ≤ Erpow) :
--       Real.rpow Z1 r ≤ Crpow * (k : Error) * (params.m : Error) * Erpow
--   ```
--
--   **Formalization Note** `MIPStarRE.LDT.Test.rpow_Z1_factor_le` is declared in `MIPRE/Background/LIDT/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/EnvelopeBounds.lean`, lines 435–499. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/EnvelopeBounds.lean#L435-L499

import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.SetLike.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Nonempty
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Definitions.Def_MIPRE_Background_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_EnvelopeBounds

open MIPStarRE
open MIPStarRE.LDT
open MIPStarRE.LDT.Test
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem MIPStarRE.LDT.Test.rpow_Z1_factor_le {params : Parameters} {k : ℕ}
    {Z1 k2 m4 E2048 r Crpow Erpow : Error}
    (hZ1NN : 0 ≤ Z1)
    (hZ1 : Z1 ≤ 20204 * k2 * m4 * E2048)
    (hrNN : 0 ≤ r)
    (hk2NN : 0 ≤ k2)
    (hm4NN : 0 ≤ m4)
    (hE2048NN : 0 ≤ E2048)
    (hA : Real.rpow (20204 : Error) r ≤ Crpow)
    (hB : Real.rpow k2 r ≤ (k : Error))
    (hC : Real.rpow m4 r ≤ (params.m : Error))
    (hD : Real.rpow E2048 r ≤ Erpow) :
    Real.rpow Z1 r ≤ Crpow * (k : Error) * (params.m : Error) * Erpow := by sorry
