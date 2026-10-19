-- Prove2me | Theorems.Thm_MIPRE_Introspection_TypedEstimates_hiding_next_accepts_guarded
-- name    : MIPRE.Introspection.TypedEstimates.hiding_next_accepts_guarded
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:16:44.032712+00:00
-- url     : https://prove2.me/theorems/eace561e-6c91-45c2-aab8-6c7fbc993191
-- title:
--   The actual parsed check implies equality of the guarded coarse outcomes
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.HidingMaps` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Guarded coarse maps for the actual adjacent hiding test. The earlier fine label retains only its preceding prefix, current dual output, and remaining tail. The next map uses the later prefix as a key. A separate dummy outcome handles malformed answers and prefix mismatches, so each keyed map is total on the entire answer alphabet and defines a complete measurement.
--
--   The actual parsed check implies equality of the guarded coarse outcomes.
--   No support or in-image hypothesis on the answers is used.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open MIPRE.Introspection.TypedEstimates
--   open Finset Matrix Classical
--   variable {PauliType PauliAnswer F ι κ A H K : Type*}
--
--   theorem MIPRE.Introspection.TypedEstimates.hiding_next_accepts_guarded
--       [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
--       [Fintype F] [DecidableEq F] [Fintype A]
--       (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
--       (projectPauli : PauliAnswer → ι → F)
--       (D : (ι → F) → (ι → F) → A → A → Bool)
--       (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
--       (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
--       (hL : (L w).SupportedOn univ)
--       {a b : ParsedAnswer (ι → F) A PauliAnswer}
--       (h : TypedPredicate.check L X Z projectPauli D DP
--         (QuestionType.hide w k) (QuestionType.hide w j) a b = true) :
--       hidingNextGuarded (L w) k.val (hidingNextLater (L w) k.val b).1
--         (hidingCoarse (L w) k.val a) = (hidingNextLater (L w) k.val b).2
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.TypedEstimates.hiding_next_accepts_guarded` is declared in `MIPRE/Foundations/Introspection/HidingMaps.lean`, lines 59–94. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/HidingMaps.lean#L59-L94; blueprint lem:intro-guarded-hiding-maps

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_GameTransport
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
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_Types
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix
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
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterMixing
import Definitions.Def_MIPRE_Foundations_Introspection_RegisterCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_AuxiliaryChecks
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPredicate
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_HidingMaps

open MIPRE
open MIPRE.Introspection
open MIPRE.Introspection.TypedEstimates
open Finset Matrix Classical
variable {PauliType PauliAnswer F ι κ A H K : Type*}
  [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

theorem MIPRE.Introspection.TypedEstimates.hiding_next_accepts_guarded
    [Fintype PauliType] [DecidableEq PauliType] [Fintype PauliAnswer]
    [Fintype F] [DecidableEq F] [Fintype A]
    (L : Bool → CL.CLFun F ι ℓ) (X Z : PauliType)
    (projectPauli : PauliAnswer → ι → F)
    (D : (ι → F) → (ι → F) → A → A → Bool)
    (DP : PauliType → PauliType → PauliAnswer → PauliAnswer → Bool)
    (w : Bool) (k j : Fin ℓ) (hk : k.val + 1 = j.val)
    (hL : (L w).SupportedOn univ)
    {a b : ParsedAnswer (ι → F) A PauliAnswer}
    (h : TypedPredicate.check L X Z projectPauli D DP
      (QuestionType.hide w k) (QuestionType.hide w j) a b = true) :
    hidingNextGuarded (L w) k.val (hidingNextLater (L w) k.val b).1
      (hidingCoarse (L w) k.val a) = (hidingNextLater (L w) k.val b).2 := by sorry
