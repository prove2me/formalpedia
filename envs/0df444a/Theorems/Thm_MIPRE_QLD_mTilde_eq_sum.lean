-- Prove2me | Theorems.Thm_MIPRE_QLD_mTilde_eq_sum
-- name    : MIPRE.QLD.mTilde_eq_sum
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:42:53.504076+00:00
-- url     : https://prove2.me/theorems/fb6c8636-020a-4914-b728-37dc00e0cb5f
-- title:
--   The same sum indexed by the *pair* outcomes, which is the form the factorization starts from
-- statement:
--   A statement of the module `MIPRE.Background.QLD.ExactPauli` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Exact Pauli observables from a simultaneous pair measurement. Blueprint `lem:qld-exact-paulis`, the part of it that is **exact**: given a projective measurement `S` whose outcomes are *pairs* `(g_X, g_Z)` and a map `cd` sending an outcome to a vector of `F_q^n`, the appendix builds binary observables on the enlarged space `dA (x) (C^q)^{(x) n}` which satisfy the generalized Pauli relations with no error term at all. This file is that construction and those relations. Nothing here is approximate, and nothing here mentions the game: every statement is an identity between matrices, with `IsPVM…
--
--   The same sum indexed by the *pair* outcomes, which is the form the factorization starts
--   from.
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
--   variable (S : G × G → Matrix dA dA ℂ) (pi : G × G → G) (cd : G → (n → F))
--
--   theorem MIPRE.QLD.mTilde_eq_sum (u : n → F) (a : F) :
--       mTilde S pi cd w u a = ∑ p, S p ⊗ₖ syn w u (dotF (cd (pi p)) u + a)
--   ```
--
--   **Formalization Note** `MIPRE.QLD.mTilde_eq_sum` is declared in `MIPRE/Background/QLD/ExactPauli.lean`, lines 163–167. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/ExactPauli.lean#L163-L167; blueprint lem:qld-exact-paulis

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
variable (S : G × G → Matrix dA dA ℂ) (pi : G × G → G) (cd : G → (n → F))
  (w : (n → F) → Matrix (n → F) (n → F) ℂ)

theorem MIPRE.QLD.mTilde_eq_sum (u : n → F) (a : F) :
    mTilde S pi cd w u a = ∑ p, S p ⊗ₖ syn w u (dotF (cd (pi p)) u + a) := by sorry
