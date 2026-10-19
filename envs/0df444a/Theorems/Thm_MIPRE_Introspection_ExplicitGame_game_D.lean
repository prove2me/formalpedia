-- Prove2me | Theorems.Thm_MIPRE_Introspection_ExplicitGame_game_D
-- name    : MIPRE.Introspection.ExplicitGame.game_D
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T03:51:55.188594+00:00
-- url     : https://prove2.me/theorems/55d2b2b7-b115-47ff-a98d-0507b28c2265
-- title:
--   Exact decision equality on all raw questions and all parsed answers
-- statement:
--   A statement of the module `MIPRE.Background.Introspection.ExplicitGame` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Full typed introspection under an explicit Pauli seed enumeration. The equivalence acts on all raw questions, preserves the type, and fixes the auxiliary questions and both distinguished Pauli measurements. A permutation of the common random content proves equality of the full question-pair law, including mixed Pauli/auxiliary edges. The parsed predicate is intertwined on every question and every answer, including malformed answers and loops.
--
--   Exact decision equality on all raw questions and all parsed answers.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open MIPRE.Introspection.ExplicitGame
--   open Finset Classical
--   open MIPRE.QLD.PauliCL
--   open MIPRE.QLD.PauliCL.ExplicitSeed
--   variable {F F₀ ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
--   variable (hm : m ∣ Fintype.card F) (χ : F → Fin m) (π : F ≃ F)
--
--   theorem MIPRE.Introspection.ExplicitGame.game_D (q r : Question m t ℓ)
--       (a a' : ParsedAnswer (ι → F₀) A (QLD.Answer F m d)) :
--       (game hm χ π b L project D).D q r a a' =
--         (PauliRestriction.fullGame hm b L project D).D
--           (questionEquiv π b q) (questionEquiv π b r) a a'
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.ExplicitGame.game_D` is declared in `MIPRE/Background/Introspection/ExplicitGame.lean`, lines 132–149. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/Introspection/ExplicitGame.lean#L132-L149; blueprint lem:intro-numbered-transport

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Pi
import Mathlib.Order.Fin.Basic
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_SAT_Pcp
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
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
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Introspection_SeedSelectorProg
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Background_QLD_Game
import Definitions.Def_MIPRE_Background_QLD_CLPresentation
import Definitions.Def_MIPRE_Background_QLD_CLBinary
import Definitions.Def_MIPRE_Background_QLD_CLExplicitSeed
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
import Definitions.Def_MIPRE_Foundations_Introspection_PauliRestriction
import Definitions.Def_MIPRE_Background_QLD_CLTransport
import Definitions.Def_MIPRE_Background_Introspection_PauliRestriction
import Definitions.Def_MIPRE_Background_QLD_CLExplicitTransport
import Definitions.Def_MIPRE_Foundations_GameTransportProjection
import Definitions.Def_MIPRE_Background_Introspection_ExplicitGame

open MIPRE
open MIPRE.Introspection
open MIPRE.Introspection.ExplicitGame
open Finset Classical
open MIPRE.QLD.PauliCL
open MIPRE.QLD.PauliCL.ExplicitSeed
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000
variable {F F₀ ι A : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Algebra (ZMod 2) F] [Field F₀] [Fintype F₀] [DecidableEq F₀]
  [Fintype ι] [DecidableEq ι] [Fintype A] {m t d ℓ : ℕ} [NeZero m]
variable (hm : m ∣ Fintype.card F) (χ : F → Fin m) (π : F ≃ F)
  (hχ : ∀ s, LIDT.CL.chi hm (π s) = χ s)
  (b : Module.Basis (Fin t) (ZMod 2) F)
  (L : Bool → CL.CLFun F₀ ι ℓ) (project : QLD.Answer F m d → ι → F₀)
  (D : (ι → F₀) → (ι → F₀) → A → A → Bool)

theorem MIPRE.Introspection.ExplicitGame.game_D (q r : Question m t ℓ)
    (a a' : ParsedAnswer (ι → F₀) A (QLD.Answer F m d)) :
    (game hm χ π b L project D).D q r a a' =
      (PauliRestriction.fullGame hm b L project D).D
        (questionEquiv π b q) (questionEquiv π b r) a a' := by sorry
