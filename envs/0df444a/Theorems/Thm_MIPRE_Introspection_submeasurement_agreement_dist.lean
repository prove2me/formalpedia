-- Prove2me | Theorems.Thm_MIPRE_Introspection_submeasurement_agreement_dist
-- name    : MIPRE.Introspection.submeasurement_agreement_dist
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:14:10.88899+00:00
-- url     : https://prove2.me/theorems/abb09554-1f8a-4896-9ef0-4b45550cc055
-- title:
--   Agreement with a positive submeasurement controls distance to a PVM
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.ConditionalConsistency` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Conditional consistency. The paper's `lem:conditional-consistency`, with constant two in the summed squared state norm. The conditioning index may determine Alice's entire POVM.
--
--   Agreement with a positive submeasurement controls distance to a PVM.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder Kronecker
--   variable {N I : Type*} [Fintype N] [DecidableEq N] [Fintype I]
--
--   theorem MIPRE.Introspection.submeasurement_agreement_dist (ψ : N → ℂ) (hψ : ‖evec ψ‖ = 1)
--       (P C : I → Matrix N N ℂ) (hP : IsPVM P)
--       (hC0 : ∀ i, 0 ≤ C i) (hCsum : ∑ i, C i ≤ 1) :
--       (∑ i, snorm ψ (P i - C i) ^ 2) ≤
--         2 * (1 - ∑ i, qform ψ (P i * C i))
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.submeasurement_agreement_dist` is declared in `MIPRE/Foundations/Introspection/ConditionalConsistency.lean`, lines 22–50. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/ConditionalConsistency.lean#L22-L50; blueprint lem:conditional-measurement

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

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
variable {N I : Type*} [Fintype N] [DecidableEq N] [Fintype I]

theorem MIPRE.Introspection.submeasurement_agreement_dist (ψ : N → ℂ) (hψ : ‖evec ψ‖ = 1)
    (P C : I → Matrix N N ℂ) (hP : IsPVM P)
    (hC0 : ∀ i, 0 ≤ C i) (hCsum : ∑ i, C i ≤ 1) :
    (∑ i, snorm ψ (P i - C i) ^ 2) ≤
      2 * (1 - ∑ i, qform ψ (P i * C i)) := by sorry
