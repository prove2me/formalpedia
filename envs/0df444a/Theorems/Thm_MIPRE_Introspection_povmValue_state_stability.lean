-- Prove2me | Theorems.Thm_MIPRE_Introspection_povmValue_state_stability
-- name    : MIPRE.Introspection.povmValue_state_stability
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:39:54.164442+00:00
-- url     : https://prove2.me/theorems/504f373d-16b3-4517-b9f3-1569b82d7141
-- title:
--   The full normalized question distribution preserves the same state-replacement bound
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.StateStability` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Replacing the state after Pauli extraction. For fixed projective measurements, changing two normalized state vectors by squared norm `eta` changes every test, and the whole game value, by at most `2 sqrt(eta)`. This supplies the actual value estimate used with the state approximation in introspection, in addition to its scalar error absorption.
--
--   The full normalized question distribution preserves the same state-replacement bound.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open Finset Matrix Classical
--   open scoped Kronecker ComplexOrder MatrixOrder
--   variable {N C : Type*} [Fintype N] [DecidableEq N] [Fintype C] [DecidableEq C]
--   variable {X Y A B H K : Type*} [Fintype X] [Fintype Y]
--
--   theorem MIPRE.Introspection.povmValue_state_stability (G : Game X Y A B) (ψ φ : H × K → ℂ)
--       (hψ : ‖evec ψ‖ = 1) (hφ : ‖evec φ‖ = 1)
--       (MA : X → POVM A H) (MB : Y → POVM B K)
--       (hMA : ∀ x, IsPVM (fun a => ((MA x).mats a).val))
--       (hMB : ∀ y, IsPVM (fun b => ((MB y).mats b).val))
--       {η : ℝ} (hd : ‖evec (ψ - φ)‖ ^ 2 ≤ η) :
--       |povmValue G ψ MA MB - povmValue G φ MA MB| ≤ 2 * Real.sqrt η
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.povmValue_state_stability` is declared in `MIPRE/Foundations/Introspection/StateStability.lean`, lines 91–119. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/StateStability.lean#L91-L119; blueprint lem:intro-value-stability

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
variable {X Y A B H K : Type*} [Fintype X] [Fintype Y]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

theorem MIPRE.Introspection.povmValue_state_stability (G : Game X Y A B) (ψ φ : H × K → ℂ)
    (hψ : ‖evec ψ‖ = 1) (hφ : ‖evec φ‖ = 1)
    (MA : X → POVM A H) (MB : Y → POVM B K)
    (hMA : ∀ x, IsPVM (fun a => ((MA x).mats a).val))
    (hMB : ∀ y, IsPVM (fun b => ((MB y).mats b).val))
    {η : ℝ} (hd : ‖evec (ψ - φ)‖ ^ 2 ≤ η) :
    |povmValue G ψ MA MB - povmValue G φ MA MB| ≤ 2 * Real.sqrt η := by sorry
