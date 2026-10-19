-- Prove2me | Theorems.Thm_MIPRE_QLD_sum_sub_le_of_eq_on
-- name    : MIPRE.QLD.sum_sub_le_of_eq_on
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:54:11.022157+00:00
-- url     : https://prove2.me/theorems/752de9cc-ab4b-4c01-83ee-99da4c65aab4
-- title:
--   The substitution error. Two families that agree on ML and are each dominated in absolute value by S differ in total by at most twice the mass off ML
-- statement:
--   A statement of the module `MIPRE.Background.QLD.NonMultilinear` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The non-multilinear mass, and Schwartz--Zippel in the agreement direction. This file is the repair of the campaign's critical finding at ledger node `1.2.2.15`, recorded in blueprint `rem:qld-admitted`. The separating stage of the appendix needs to replace, inside a Born average, the evaluation `g(u)` of an outcome `g` of individual degree at most `d` by the evaluation `Coded(g) . ind_m(u)` --- which is the evaluation at `u` of the *multilinear* interpolant of `g`'s values on the cube `{0,1}^m`. The two agree for multilinear `g` and not otherwise. An earlier revision of the paper bounded the…
--
--   **The substitution error.** Two families that agree on `ML` and are each dominated in absolute
--   value by `S` differ in total by at most twice the mass off `ML`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset MvPolynomial MIPRE.LowDegree
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ}
--   variable {G : Type*} [Fintype G] [DecidableEq G]
--
--   theorem MIPRE.QLD.sum_sub_le_of_eq_on {A B S : G → ℝ} {ML : Finset G}
--       (hon : ∀ g ∈ ML, A g = B g) (hA : ∀ g, |A g| ≤ S g) (hB : ∀ g, |B g| ≤ S g) :
--       |∑ g, A g - ∑ g, B g| ≤ 2 * ∑ g ∈ univ \ ML, S g
--   ```
--
--   **Formalization Note** `MIPRE.QLD.sum_sub_le_of_eq_on` is declared in `MIPRE/Background/QLD/NonMultilinear.lean`, lines 120–138. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/NonMultilinear.lean#L120-L138; blueprint lem:qld-exact-paulis

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel

open MIPRE
open Finset MvPolynomial MIPRE.LowDegree
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ}
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem MIPRE.QLD.sum_sub_le_of_eq_on {A B S : G → ℝ} {ML : Finset G}
    (hon : ∀ g ∈ ML, A g = B g) (hA : ∀ g, |A g| ≤ S g) (hB : ∀ g, |B g| ≤ S g) :
    |∑ g, A g - ∑ g, B g| ≤ 2 * ∑ g ∈ univ \ ML, S g := by sorry
