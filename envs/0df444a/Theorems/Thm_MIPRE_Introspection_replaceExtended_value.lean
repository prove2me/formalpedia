-- Prove2me | Theorems.Thm_MIPRE_Introspection_replaceExtended_value
-- name    : MIPRE.Introspection.replaceExtended_value
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:40:26.921818+00:00
-- url     : https://prove2.me/theorems/303365b4-2fc0-46d6-a7d1-efa572cf9685
-- title:
--   Quantitative value preservation for the actual replacement family
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.StrategyReplacement` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Replacing one measurement on a common ancillary extension. The new family is a function of the actual question. The selected question uses the supplied projective dilation; every other measurement is the old measurement tensored with identity. The state extension is independent of the question and the opposite player is unchanged.
--
--   Quantitative value preservation for the actual replacement family.
--   The fine outcomes may be relabelled by any function, including a constructor
--   in the common parsed-answer alphabet.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open Finset Matrix Classical
--   open scoped Kronecker
--   variable {X Y A B C H K T : Type*}
--
--   theorem MIPRE.Introspection.replaceExtended_value (G : Game X Y A B) (ψ : H × K → ℂ)
--       (hψ : ‖evec ψ‖ = 1) (a₀ : T)
--       (MA : X → POVM A H) (MB : Y → POVM B K)
--       (q : X) (M : POVM C H) (R : POVM C (H × T)) (f : C → A)
--       (hMA : MA q = M.map f) (hM : IsPVM fun c => (M.mats c).val)
--       (hR : IsPVM fun c => (R.mats c).val)
--       (hMB : ∀ y, IsPVM fun b => ((MB y).mats b).val) {δ : ℝ}
--       (hd : ∑ c, stateSqNorm (extVecA ψ a₀)
--         (aOp (M.mats c).val - (R.mats c).val) ≤ δ) :
--       |povmValue G ψ MA MB -
--         povmValue G (extVecA ψ a₀) (replaceExtended MA q (R.map f)) MB| ≤ 2*Real.sqrt δ
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.replaceExtended_value` is declared in `MIPRE/Foundations/Introspection/StrategyReplacement.lean`, lines 64–88. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/StrategyReplacement.lean#L64-L88; blueprint lem:intro-adaptive-strategy

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
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
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
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_POVMMix_B
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_StrategyDilation
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterTransport
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterEPR
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability
import Definitions.Def_MIPRE_Foundations_Introspection_HidingInductionDilation
import Definitions.Def_MIPRE_Foundations_Introspection_StrategyReplacement

open MIPRE
open MIPRE.Introspection
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {X Y A B C H K T : Type*}
  [Fintype X] [DecidableEq X] [Fintype Y]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype T] [DecidableEq T]

theorem MIPRE.Introspection.replaceExtended_value (G : Game X Y A B) (ψ : H × K → ℂ)
    (hψ : ‖evec ψ‖ = 1) (a₀ : T)
    (MA : X → POVM A H) (MB : Y → POVM B K)
    (q : X) (M : POVM C H) (R : POVM C (H × T)) (f : C → A)
    (hMA : MA q = M.map f) (hM : IsPVM fun c => (M.mats c).val)
    (hR : IsPVM fun c => (R.mats c).val)
    (hMB : ∀ y, IsPVM fun b => ((MB y).mats b).val) {δ : ℝ}
    (hd : ∑ c, stateSqNorm (extVecA ψ a₀)
      (aOp (M.mats c).val - (R.mats c).val) ≤ δ) :
    |povmValue G ψ MA MB -
      povmValue G (extVecA ψ a₀) (replaceExtended MA q (R.map f)) MB| ≤ 2*Real.sqrt δ := by sorry
