-- Prove2me | Theorems.Thm_MIPStarRE_LDT_Test_zeta1_bound
-- name    : MIPStarRE.LDT.Test.zeta1_bound
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:16:51.542561+00:00
-- url     : https://prove2.me/theorems/29fa2d2c-ac78-4406-9192-b0da00f1fb78
-- title:
--   Paper lines 196–201. The concrete ζ₁ built from σ = cascadeSigma params k ν is absorbed by mainFormalError
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.MIPStarRE.LDT.Test.MainTheorem.ScalarBounds.CascadeBounds.SigmaZeta1` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Error cascade — bounds for `σ` and `ζ₁`. This module proves the tight and absorbing bounds for the first two cascade variables, `σ` and `ζ₁`. The later variables `ζ₂`, `ζ₃`, and `ζ₄`, together with the top-level consolidator `errorCascade_le_mainFormalError`, are in the subsequent leaves of `Test.MainTheorem.ScalarBounds.CascadeBounds`. The first cascade steps have three components: * The **tight cascade bound** (`cascadeSigma_tight_bound`, `cascadeZeta1_bound`, …), deriving the native estimate directly from the cascade definition. * The **absorbing bound** (`sigma_bound`, `zeta1_bound`, …),…
--
--   The module is vendored read-only, with the authors' permission, from [LionSR/MIPStarRE](https://github.com/LionSR/MIPStarRE) (Sirui Lu and the MIPStarRE contributors, Apache 2.0; commit and upstream path in the file header) by `scripts/vendor-lidt.py`.
--
--   **Paper lines 196–201.** The concrete `ζ₁` built from `σ = cascadeSigma params k ν`
--   is absorbed by `mainFormalError`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPStarRE
--   open MIPStarRE.LDT
--   open MIPStarRE.LDT.Test
--   open scoped BigOperators
--
--   theorem MIPStarRE.LDT.Test.zeta1_bound {params : Parameters} {k : ℕ} {eps : Error}
--       (h : CascadeHypotheses params k eps) {ν σ : Error}
--       (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
--         (Real.rpow eps (1 / (1024 : Error)) +
--           Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))))
--       (hσEq : σ = cascadeSigma params k ν) :
--       cascadeZeta1 params eps σ ≤ mainFormalError params k eps
--   ```
--
--   **Formalization Note** `MIPStarRE.LDT.Test.zeta1_bound` is declared in `MIPRE/Background/LIDT/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/CascadeBounds/SigmaZeta1.lean`, lines 479–512. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/MIPStarRE/LDT/Test/MainTheorem/ScalarBounds/CascadeBounds/SigmaZeta1.lean#L479-L512

import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
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
import Mathlib.Algebra.Order.Group.Defs
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
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
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
import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Rat.Init
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
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
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

theorem MIPStarRE.LDT.Test.zeta1_bound {params : Parameters} {k : ℕ} {eps : Error}
    (h : CascadeHypotheses params k eps) {ν σ : Error}
    (hν : ν ≤ 10000 * ((k : Error) ^ (2 : ℕ)) * ((params.m : Error) ^ (2 : ℕ)) *
      (Real.rpow eps (1 / (1024 : Error)) +
        Real.rpow ((params.d : Error) / (params.q : Error)) (1 / (1024 : Error))))
    (hσEq : σ = cascadeSigma params k ν) :
    cascadeZeta1 params eps σ ≤ mainFormalError params k eps := by sorry
