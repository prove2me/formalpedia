-- Prove2me | Theorems.Thm_MIPRE_Introspection_submeasurement_completion_mass
-- name    : MIPRE.Introspection.submeasurement_completion_mass
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:39:57.612974+00:00
-- url     : https://prove2.me/theorems/bfc26068-901e-48fc-b003-589f848318a5
-- title:
--   Completing a positive submeasurement dominated by a POVM costs at most its missing mass
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.SubmeasurementCompletion` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Completing a nearby submeasurement. The paper's `lem:replace-with-measurement`, with the explicit estimate `2 δ + 4 sqrt δ` for the squared state norm. The outcome alphabet contributes no factor.
--
--   Completing a positive submeasurement dominated by a POVM costs at most its missing mass.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder
--   variable {N A : Type*} [Fintype N] [DecidableEq N] [Fintype A] [DecidableEq A]
--
--   theorem MIPRE.Introspection.submeasurement_completion_mass (ψ : N → ℂ) (hψ : ‖evec ψ‖ = 1)
--       (B C : A → Matrix N N ℂ) (hB : ∀ a, 0 ≤ B a) (hC : ∀ a, 0 ≤ C a)
--       (hCsum : ∑ a, C a = 1) (hBC : ∀ a, B a ≤ C a) :
--       (∑ a, snorm ψ (B a - C a) ^ 2) ≤ 1 - ∑ a, qform ψ (B a)
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.submeasurement_completion_mass` is declared in `MIPRE/Foundations/Introspection/SubmeasurementCompletion.lean`, lines 22–37. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/SubmeasurementCompletion.lean#L22-L37; blueprint lem:close-submeasurement

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
open scoped ComplexOrder MatrixOrder
variable {N A : Type*} [Fintype N] [DecidableEq N] [Fintype A] [DecidableEq A]

theorem MIPRE.Introspection.submeasurement_completion_mass (ψ : N → ℂ) (hψ : ‖evec ψ‖ = 1)
    (B C : A → Matrix N N ℂ) (hB : ∀ a, 0 ≤ B a) (hC : ∀ a, 0 ≤ C a)
    (hCsum : ∑ a, C a = 1) (hBC : ∀ a, B a ≤ C a) :
    (∑ a, snorm ψ (B a - C a) ^ 2) ≤ 1 - ∑ a, qform ψ (B a) := by sorry
