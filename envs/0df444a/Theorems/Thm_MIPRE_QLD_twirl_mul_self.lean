-- Prove2me | Theorems.Thm_MIPRE_QLD_twirl_mul_self
-- name    : MIPRE.QLD.twirl_mul_self
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:46:48.628551+00:00
-- url     : https://prove2.me/theorems/c07a8746-5891-4a9f-b79c-e3a5297da6ab
-- title:
--   The twirl is a projection. The Weyl family is a homomorphism, so the double average collapses: for each s there are exactly q^n pairs (u, v) with u + v = s
-- statement:
--   A statement of the module `MIPRE.Background.QLD.SwapState` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The swap isometry's state estimate (`lem:qld-swap`, item 1). `MIPRE/Background/QLD/SwapUnitary.lean` proves the two halves of item 1 separately: the algebra (`swapU_conj_wTilde_X`, `swapU_conj_wTilde_Z`: conjugation by the swap map carries the exact Pauli observables to bare generalized Paulis, with no error at all), the identity the estimate rests on (`twirl_mul_twirl`: the product of the two Weyl twirls is the maximally entangled projector), and the arithmetic that turns two near-invariances into a closeness (`norm_sub_sq_le_of_re_inner_ge`, `re_inner_ge_of_two_close`,…
--
--   **The twirl is a projection.** The Weyl family is a homomorphism, so the double average
--   collapses: for each `s` there are exactly `q^n` pairs `(u, v)` with `u + v = s`.
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
--
--   theorem MIPRE.QLD.twirl_mul_self {w : (n → F) → Matrix (n → F) (n → F) ℂ} (hw : IsWeylFamily w) :
--       twirl w * twirl w = twirl w
--   ```
--
--   **Formalization Note** `MIPRE.QLD.twirl_mul_self` is declared in `MIPRE/Background/QLD/SwapState.lean`, lines 105–120. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/QLD/SwapState.lean#L105-L120; blueprint lem:qld-swap

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Background_QLD_ExactPauli
import Definitions.Def_MIPRE_Background_QLD_SwapUnitary
import Definitions.Def_MIPRE_Background_QLD_SwapState

open MIPRE
open MIPRE.QLD
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem MIPRE.QLD.twirl_mul_self {w : (n → F) → Matrix (n → F) (n → F) ℂ} (hw : IsWeylFamily w) :
    twirl w * twirl w = twirl w := by sorry
