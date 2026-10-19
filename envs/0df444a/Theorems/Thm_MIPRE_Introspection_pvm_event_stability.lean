-- Prove2me | Theorems.Thm_MIPRE_Introspection_pvm_event_stability
-- name    : MIPRE.Introspection.pvm_event_stability
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:41:26.228496+00:00
-- url     : https://prove2.me/theorems/6f7471de-49c3-4579-86f7-b710b57b2090
-- title:
--   Changing a projective measurement by squared distance delta changes the probability of any event by at most 2 sqrt(delta), with no outcome-count factor
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.ValueStability` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Value stability for the introspection induction. The induction replaces projective measurements using summed squared state distance. The resulting change in test acceptance is dimension independent: `2 sqrt(delta)` per party. Summing outcomes before Cauchy--Schwarz avoids any loss depending on the size of the introspection answer alphabet.
--
--   Changing a projective measurement by squared distance `delta` changes the
--   probability of any event by at most `2 sqrt(delta)`, with no outcome-count factor.
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
--   theorem MIPRE.Introspection.pvm_event_stability (v : N → ℂ) (hv : ‖evec v‖ = 1)
--       {M R : C → Matrix N N ℂ} (hM : IsPVM M) (hR : IsPVM R)
--       (s : Finset C) {δ : ℝ} (hd : ∑ c, snorm v (M c - R c) ^ 2 ≤ δ) :
--       |(∑ c ∈ s, qform v (M c)) - ∑ c ∈ s, qform v (R c)| ≤ 2 * Real.sqrt δ
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.pvm_event_stability` is declared in `MIPRE/Foundations/Introspection/ValueStability.lean`, lines 58–93. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/ValueStability.lean#L58-L93; blueprint lem:intro-value-stability

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

theorem MIPRE.Introspection.pvm_event_stability (v : N → ℂ) (hv : ‖evec v‖ = 1)
    {M R : C → Matrix N N ℂ} (hM : IsPVM M) (hR : IsPVM R)
    (s : Finset C) {δ : ℝ} (hd : ∑ c, snorm v (M c - R c) ^ 2 ≤ δ) :
    |(∑ c ∈ s, qform v (M c)) - ∑ c ∈ s, qform v (R c)| ≤ 2 * Real.sqrt δ := by sorry
