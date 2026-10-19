-- Prove2me | Theorems.Thm_MIPRE_Introspection_povmValue_stability_at
-- name    : MIPRE.Introspection.povmValue_stability_at
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:40:08.001106+00:00
-- url     : https://prove2.me/theorems/16af9ef1-0eae-47e1-a616-0695edb3d989
-- title:
--   A single changed question, with an arbitrary outcome relabelling
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.StrategyReplacementValue` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Game-value bounds for actual question-indexed replacements. Acceptance is compared before relabelling the outcomes. This permits a common answer alphabet without assuming that same-party squared distance contracts under coarse-graining.
--
--   A single changed question, with an arbitrary outcome relabelling. All
--   other questions are literally unchanged, and the error pays at most its
--   conditional bound since the question's marginal probability is at most one.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open Finset Matrix Classical
--   open scoped Kronecker
--   variable {X Y A B C H K : Type*}
--
--   theorem MIPRE.Introspection.povmValue_stability_at [DecidableEq X]
--       (G : Game X Y A B) (ψ : H × K → ℂ) (hψ : ‖evec ψ‖ = 1)
--       (MA RA : X → POVM A H) (MB : Y → POVM B K)
--       (q : X) (M R : POVM C H) (f : C → A)
--       (hMA : MA q = M.map f) (hRA : RA q = R.map f)
--       (hsame : ∀ x, x ≠ q → MA x = RA x)
--       (hM : IsPVM fun c => (M.mats c).val) (hR : IsPVM fun c => (R.mats c).val)
--       (hMB : ∀ y, IsPVM fun b => ((MB y).mats b).val) {δ : ℝ}
--       (hd : ∑ c, stateSqNorm ψ ((M.mats c).val - (R.mats c).val) ≤ δ) :
--       |povmValue G ψ MA MB - povmValue G ψ RA MB| ≤ 2*Real.sqrt δ
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.povmValue_stability_at` is declared in `MIPRE/Foundations/Introspection/StrategyReplacementValue.lean`, lines 86–119. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/StrategyReplacementValue.lean#L86-L119

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
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_POVMMix_B
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability

open MIPRE
open MIPRE.Introspection
open Finset Matrix Classical
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {X Y A B C H K : Type*}
  [Fintype X] [Fintype Y] [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]

theorem MIPRE.Introspection.povmValue_stability_at [DecidableEq X]
    (G : Game X Y A B) (ψ : H × K → ℂ) (hψ : ‖evec ψ‖ = 1)
    (MA RA : X → POVM A H) (MB : Y → POVM B K)
    (q : X) (M R : POVM C H) (f : C → A)
    (hMA : MA q = M.map f) (hRA : RA q = R.map f)
    (hsame : ∀ x, x ≠ q → MA x = RA x)
    (hM : IsPVM fun c => (M.mats c).val) (hR : IsPVM fun c => (R.mats c).val)
    (hMB : ∀ y, IsPVM fun b => ((MB y).mats b).val) {δ : ℝ}
    (hd : ∑ c, stateSqNorm ψ ((M.mats c).val - (R.mats c).val) ≤ δ) :
    |povmValue G ψ MA MB - povmValue G ψ RA MB| ≤ 2*Real.sqrt δ := by sorry
