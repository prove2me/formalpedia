-- Prove2me | Theorems.Thm_MIPRE_QLD_kron_sum
-- name    : MIPRE.QLD.kron_sum
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:41:57.654197+00:00
-- url     : https://prove2.me/theorems/7b36d84c-84aa-4451-8c17-cc83c90e01e3
-- title:
--   A (x) (sum_x B x) = sum_x (A (x) B x)
-- statement:
--   A statement of the module `MIPRE.Background.QLD.ExactPauli` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Exact Pauli observables from a simultaneous pair measurement. Blueprint `lem:qld-exact-paulis`, the part of it that is **exact**: given a projective measurement `S` whose outcomes are *pairs* `(g_X, g_Z)` and a map `cd` sending an outcome to a vector of `F_q^n`, the appendix builds binary observables on the enlarged space `dA (x) (C^q)^{(x) n}` which satisfy the generalized Pauli relations with no error term at all. This file is that construction and those relations. Nothing here is approximate, and nothing here mentions the game: every statement is an identity between matrices, with `IsPVM…
--
--   `A (x) (sum_x B x) = sum_x (A (x) B x)`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.QLD
--   open Finset Matrix MIPRE MIPRE.Weyl
--   open scoped Kronecker ComplexOrder MatrixOrder
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
--   variable {n : Type*} [Fintype n] [DecidableEq n]
--   variable {G : Type*} [Fintype G] [DecidableEq G]
--   variable {dA : Type*} [Fintype dA] [DecidableEq dA]
--
--   theorem MIPRE.QLD.kron_sum {iota : Type*} (s : Finset iota) (A : Matrix dA dA ℂ)
--       (B : iota → Matrix (n → F) (n → F) ℂ) :
--       A ⊗ₖ (∑ x ∈ s, B x) = ∑ x ∈ s, A ⊗ₖ B x
--   ```
--
--   **Formalization Note** `MIPRE.QLD.kron_sum` is declared in `MIPRE/Background/QLD/ExactPauli.lean`, lines 117–125. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/ExactPauli.lean#L117-L125; blueprint lem:qld-exact-paulis

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Background_QLD_ExactPauli

open MIPRE
open MIPRE.QLD
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]

theorem MIPRE.QLD.kron_sum {iota : Type*} (s : Finset iota) (A : Matrix dA dA ℂ)
    (B : iota → Matrix (n → F) (n → F) ℂ) :
    A ⊗ₖ (∑ x ∈ s, B x) = ∑ x ∈ s, A ⊗ₖ B x := by sorry
