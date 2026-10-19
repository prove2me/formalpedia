-- Prove2me | Theorems.Thm_MIPRE_Introspection_submeasurement_extension_mass
-- name    : MIPRE.Introspection.submeasurement_extension_mass
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:41:16.852518+00:00
-- url     : https://prove2.me/theorems/f034f1aa-9052-4eb7-9210-bdc0839adf35
-- title:
--   Extending a positive submeasurement inside another submeasurement costs at most the missing mass
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.ValidOutcomeError` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Recovering all outcomes from valid-outcome extraction estimates. Pauli extraction sums only the valid full-register answers. The actual introspection induction also retains every malformed answer. Positivity and the submeasurement mass estimate extend the former guarantee to the whole mapped alphabet, without an answer-cardinality factor or a premise that malformed effects vanish.
--
--   Extending a positive submeasurement inside another submeasurement
--   costs at most the missing mass. Normalization of the extension is not needed.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open Finset Matrix Classical
--   open scoped ComplexOrder MatrixOrder
--   variable {N A B : Type*} [Fintype N] [DecidableEq N]
--
--   theorem MIPRE.Introspection.submeasurement_extension_mass (ψ : N → ℂ) (hψ : ‖evec ψ‖ = 1)
--       (M C : A → Matrix N N ℂ) (hM : ∀ a, 0 ≤ M a) (hC : ∀ a, 0 ≤ C a)
--       (hCsum : ∑ a, C a ≤ 1) (hMC : ∀ a, M a ≤ C a) :
--       (∑ a, snorm ψ (M a - C a) ^ 2) ≤ 1 - ∑ a, qform ψ (M a)
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.submeasurement_extension_mass` is declared in `MIPRE/Foundations/Introspection/ValidOutcomeError.lean`, lines 26–46. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/ValidOutcomeError.lean#L26-L46; blueprint lem:intro-valid-isometric-soundness

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
import Definitions.Def_MIPRE_Foundations_Introspection_IsometricStrategy

open MIPRE
open MIPRE.Introspection
open Finset Matrix Classical
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N A B : Type*} [Fintype N] [DecidableEq N]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

theorem MIPRE.Introspection.submeasurement_extension_mass (ψ : N → ℂ) (hψ : ‖evec ψ‖ = 1)
    (M C : A → Matrix N N ℂ) (hM : ∀ a, 0 ≤ M a) (hC : ∀ a, 0 ≤ C a)
    (hCsum : ∑ a, C a ≤ 1) (hMC : ∀ a, M a ≤ C a) :
    (∑ a, snorm ψ (M a - C a) ^ 2) ≤ 1 - ∑ a, qform ψ (M a) := by sorry
