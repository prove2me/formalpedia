-- Prove2me | Theorems.Thm_MIPRE_Introspection_povmValue_stability_of_condWin
-- name    : MIPRE.Introspection.povmValue_stability_of_condWin
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:40:09.622622+00:00
-- url     : https://prove2.me/theorems/d4d2dc4e-43ce-4839-b28d-fe3eb0b7263d
-- title:
--   Averaging conditional acceptance changes costs no question-count factor
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.StrategyReplacementValue` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Game-value bounds for actual question-indexed replacements. Acceptance is compared before relabelling the outcomes. This permits a common answer alphabet without assuming that same-party squared distance contracts under coarse-graining.
--
--   Averaging conditional acceptance changes costs no question-count factor.
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
--   theorem MIPRE.Introspection.povmValue_stability_of_condWin (G : Game X Y A B) (ψ : H × K → ℂ)
--       (MA RA : X → POVM A H) (MB : Y → POVM B K)
--       (err : X → ℝ) (herr : ∀ x, 0 ≤ err x)
--       (hpoint : ∀ x y, |condWin G ψ MA MB x y - condWin G ψ RA MB x y| ≤
--         2*Real.sqrt (err x)) {δ : ℝ}
--       (hd : ∑ x, ∑ y, G.μ x y * err x ≤ δ) :
--       |povmValue G ψ MA MB - povmValue G ψ RA MB| ≤ 2*Real.sqrt δ
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.povmValue_stability_of_condWin` is declared in `MIPRE/Foundations/Introspection/StrategyReplacementValue.lean`, lines 52–84. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/StrategyReplacementValue.lean#L52-L84

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

theorem MIPRE.Introspection.povmValue_stability_of_condWin (G : Game X Y A B) (ψ : H × K → ℂ)
    (MA RA : X → POVM A H) (MB : Y → POVM B K)
    (err : X → ℝ) (herr : ∀ x, 0 ≤ err x)
    (hpoint : ∀ x y, |condWin G ψ MA MB x y - condWin G ψ RA MB x y| ≤
      2*Real.sqrt (err x)) {δ : ℝ}
    (hd : ∑ x, ∑ y, G.μ x y * err x ≤ δ) :
    |povmValue G ψ MA MB - povmValue G ψ RA MB| ≤ 2*Real.sqrt δ := by sorry
