-- Prove2me | Theorems.Thm_MIPRE_QLD_nonMultilinear_mass_le
-- name    : MIPRE.QLD.nonMultilinear_mass_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:54:14.066139+00:00
-- url     : https://prove2.me/theorems/4cc8714e-4396-48af-954d-e9a5a7a3a904
-- title:
--   The mass bound. If T is dominated by the distribution S, is at most c times S away from the good set ML, and still carries total weight at least 1 - eta, then S…
-- statement:
--   A statement of the module `MIPRE.Background.QLD.NonMultilinear` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The non-multilinear mass, and Schwartz--Zippel in the agreement direction. This file is the repair of the campaign's critical finding at ledger node `1.2.2.15`, recorded in blueprint `rem:qld-admitted`. The separating stage of the appendix needs to replace, inside a Born average, the evaluation `g(u)` of an outcome `g` of individual degree at most `d` by the evaluation `Coded(g) . ind_m(u)` --- which is the evaluation at `u` of the *multilinear* interpolant of `g`'s values on the cube `{0,1}^m`. The two agree for multilinear `g` and not otherwise. An earlier revision of the paper bounded the…
--
--   **The mass bound.** If `T` is dominated by the distribution `S`, is at most `c` times `S` away
--   from the good set `ML`, and still carries total weight at least `1 - eta`, then `S` puts at most
--   `eta + c` off `ML`.
--
--   This is the appendix's aggregation step, and it is the shape the repaired argument needs: the
--   agreement bound of `prob_agree_ldEnc_le_of_not_multilinear` is exactly the hypothesis `hoff` at
--   `c = md/q`. The proof is one split of the total: on `ML` only the domination `T <= S` is available,
--   off `ML` the agreement bound applies, and comparing with `sum S = 1` isolates the mass off `ML`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset MvPolynomial MIPRE.LowDegree
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d : ℕ}
--   variable {G : Type*} [Fintype G] [DecidableEq G]
--
--   theorem MIPRE.QLD.nonMultilinear_mass_le {S T : G → ℝ} {ML : Finset G} {c eta : ℝ}
--       (hS : ∀ g, 0 ≤ S g) (hsum : ∑ g, S g = 1) (hT : ∀ g, T g ≤ S g)
--       (hoff : ∀ g ∉ ML, T g ≤ c * S g) (hc : 0 ≤ c) (hlow : 1 - eta ≤ ∑ g, T g) :
--       ∑ g ∈ univ \ ML, S g ≤ eta + c
--   ```
--
--   **Formalization Note** `MIPRE.QLD.nonMultilinear_mass_le` is declared in `MIPRE/Background/QLD/NonMultilinear.lean`, lines 90–118. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/NonMultilinear.lean#L90-L118; blueprint lem:qld-exact-paulis

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

theorem MIPRE.QLD.nonMultilinear_mass_le {S T : G → ℝ} {ML : Finset G} {c eta : ℝ}
    (hS : ∀ g, 0 ≤ S g) (hsum : ∑ g, S g = 1) (hT : ∀ g, T g ≤ S g)
    (hoff : ∀ g ∉ ML, T g ≤ c * S g) (hc : 0 ≤ c) (hlow : 1 - eta ≤ ∑ g, T g) :
    ∑ g ∈ univ \ ML, S g ≤ eta + c := by sorry
