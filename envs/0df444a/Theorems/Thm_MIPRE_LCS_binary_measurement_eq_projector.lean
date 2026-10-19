-- Prove2me | Theorems.Thm_MIPRE_LCS_binary_measurement_eq_projector
-- name    : MIPRE.LCS.binary_measurement_eq_projector
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:13:53.33371+00:00
-- url     : https://prove2.me/theorems/77a297e1-2f68-4f60-a6ca-ee6652474bb1
-- title:
--   Lemma binary_measurement_eq_projector of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.LCS.Observable` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Observables in LCS Games. This module defines the algebraic properties of quantum observables in the context of Linear Constraint System (LCS) games. An observable is represented as a self-adjoint, involutive operator.
--
--   The module belongs to the linear constraint system games development contributed by Sean Perazzolo, vendored with permission from [sean-prz/LCS_In_Lean](https://github.com/sean-prz/LCS_In_Lean) and adapted to this repository (Apache 2.0; the author is named in the file header).
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LCS
--   variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]
--
--   theorem MIPRE.LCS.binary_measurement_eq_projector (f : ZMod 2 → R) (h : IsMeasurementSystem f) (y : ZMod 2) :
--       f y = (1 / 2 : ℂ) • (1 + (-1 : ℂ) ^ y.val • observableOfMeasurementSystem f)
--   ```
--
--   **Formalization Note** `MIPRE.LCS.binary_measurement_eq_projector` is declared in `MIPRE/LCS/Observable.lean`, lines 61–78. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/LCS/Observable.lean#L61-L78; blueprint def:observable

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable

open MIPRE
open MIPRE.LCS
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R]

theorem MIPRE.LCS.binary_measurement_eq_projector (f : ZMod 2 → R) (h : IsMeasurementSystem f) (y : ZMod 2) :
    f y = (1 / 2 : ℂ) • (1 + (-1 : ℂ) ^ y.val • observableOfMeasurementSystem f) := by sorry
