-- Prove2me | Theorems.Thm_MIPRE_Introspection_qform_state_stability
-- name    : MIPRE.Introspection.qform_state_stability
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:38:13.996904+00:00
-- url     : https://prove2.me/theorems/d87771de-9f94-4903-8c97-6c796050250c
-- title:
--   A contraction's quadratic form is Lipschitz on the unit sphere
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.StateStability` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Replacing the state after Pauli extraction. For fixed projective measurements, changing two normalized state vectors by squared norm `eta` changes every test, and the whole game value, by at most `2 sqrt(eta)`. This supplies the actual value estimate used with the state approximation in introspection, in addition to its scalar error absorption.
--
--   A contraction's quadratic form is Lipschitz on the unit sphere.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open Finset Matrix Classical
--   open scoped Kronecker ComplexOrder MatrixOrder
--   variable {N C : Type*} [Fintype N] [DecidableEq N] [Fintype C] [DecidableEq C]
--
--   theorem MIPRE.Introspection.qform_state_stability (v w : N → ℂ) (hv : ‖evec v‖ = 1) (hw : ‖evec w‖ = 1)
--       (R : Matrix N N ℂ) (hR : Bnd R 1) :
--       |qform v R - qform w R| ≤ 2 * ‖evec (v - w)‖
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.qform_state_stability` is declared in `MIPRE/Foundations/Introspection/StateStability.lean`, lines 26–48. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/StateStability.lean#L26-L48; blueprint lem:intro-value-stability

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
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability

open MIPRE
open MIPRE.Introspection
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N C : Type*} [Fintype N] [DecidableEq N] [Fintype C] [DecidableEq C]

theorem MIPRE.Introspection.qform_state_stability (v w : N → ℂ) (hv : ‖evec v‖ = 1) (hw : ‖evec w‖ = 1)
    (R : Matrix N N ℂ) (hR : Bnd R 1) :
    |qform v R - qform w R| ≤ 2 * ‖evec (v - w)‖ := by sorry
