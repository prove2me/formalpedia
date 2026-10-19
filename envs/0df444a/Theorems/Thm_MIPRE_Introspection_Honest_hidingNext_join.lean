-- Prove2me | Theorems.Thm_MIPRE_Introspection_Honest_hidingNext_join
-- name    : MIPRE.Introspection.Honest.hidingNext_join
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:22:13.171319+00:00
-- url     : https://prove2.me/theorems/b70dce22-cd54-4bd4-a10a-945d3ec46b5c
-- title:
--   The adjacent-hiding check lifts through an actual common adaptive local outcome
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.HonestHidingChecks` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Exact recursion of the honest hiding checks. Adding one common local Z/dual outcome to two supported continuation answers preserves the actual parsed hiding predicate. These are identities for the source checks, including the later-answer choice of adaptive registers.
--
--   The adjacent-hiding check lifts through an actual common adaptive local outcome.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Introspection
--   open MIPRE.Introspection.Honest
--   open Finset Matrix Classical MIPRE.Weyl
--   variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
--
--   theorem MIPRE.Introspection.Honest.hidingNext_join {S V : Finset ι} (L : CL.RegLinear F S)
--       (next : (ι → F) → CL.CLFun F ι ℓ)
--       (h : (CL.CLFun.cons S L next).SupportedOn V) (k : ℕ)
--       (z : (Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F))
--       (u v : HideLabel F ι)
--       (hu : CL.proj (V \ S) u.1 = u.1 ∧ CL.proj (V \ S) u.2.1 = u.2.1 ∧
--         CL.proj (V \ S) u.2.2 = u.2.2)
--       (hv : CL.proj (V \ S) v.1 = v.1 ∧ CL.proj (V \ S) v.2.1 = v.2.1 ∧
--         CL.proj (V \ S) v.2.2 = v.2.2)
--       (ht : CLChecks.hidingNext (next (coordinateInsert S z.1)) k u v) :
--       CLChecks.hidingNext (.cons S L next) (k + 1) (joinHide S (z, u)) (joinHide S (z, v))
--   ```
--
--   **Formalization Note** `MIPRE.Introspection.Honest.hidingNext_join` is declared in `MIPRE/Foundations/Introspection/HonestHidingChecks.lean`, lines 98–128. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/HonestHidingChecks.lean#L98-L128; blueprint lem:intro-honest-hiding

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Eval.Defs
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
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
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
import Definitions.Def_MIPRE_Foundations_Introspection_Readout
import Definitions.Def_MIPRE_Foundations_Introspection_FinalExtraction
import Definitions.Def_MIPRE_Foundations_Introspection_TypeGraph
import Definitions.Def_MIPRE_Foundations_Introspection_HonestCore
import Definitions.Def_MIPRE_Foundations_Introspection_HonestFirstHide
import Definitions.Def_MIPRE_Foundations_Introspection_HonestAdaptive
import Definitions.Def_MIPRE_Foundations_Introspection_HonestRead
import Definitions.Def_MIPRE_Foundations_Introspection_HonestXCoordinates
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingStep
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHiding
import Definitions.Def_MIPRE_Foundations_Introspection_HonestLabelSupport
import Definitions.Def_MIPRE_Foundations_Introspection_TypedPresentation
import Definitions.Def_MIPRE_Foundations_Introspection_TypedEstimates
import Definitions.Def_MIPRE_Foundations_Introspection_HidingRigidity
import Definitions.Def_MIPRE_Foundations_Introspection_HonestHidingChecks

open MIPRE
open MIPRE.Introspection
open MIPRE.Introspection.Honest
open Finset Matrix Classical MIPRE.Weyl
set_option linter.unusedSectionVars false
variable {F ι : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

theorem MIPRE.Introspection.Honest.hidingNext_join {S V : Finset ι} (L : CL.RegLinear F S)
    (next : (ι → F) → CL.CLFun F ι ℓ)
    (h : (CL.CLFun.cons S L next).SupportedOn V) (k : ℕ)
    (z : (Fin (Fintype.card S) → F) × (Fin (Fintype.card S) → F))
    (u v : HideLabel F ι)
    (hu : CL.proj (V \ S) u.1 = u.1 ∧ CL.proj (V \ S) u.2.1 = u.2.1 ∧
      CL.proj (V \ S) u.2.2 = u.2.2)
    (hv : CL.proj (V \ S) v.1 = v.1 ∧ CL.proj (V \ S) v.2.1 = v.2.1 ∧
      CL.proj (V \ S) v.2.2 = v.2.2)
    (ht : CLChecks.hidingNext (next (coordinateInsert S z.1)) k u v) :
    CLChecks.hidingNext (.cons S L next) (k + 1) (joinHide S (z, u)) (joinHide S (z, v)) := by sorry
