-- Prove2me | Theorems.Thm_MIPRE_CL_Detyping_DeciderProgram_prog_time
-- name    : MIPRE.CL.Detyping.DeciderProgram.prog_time
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:54:42.935707+00:00
-- url     : https://prove2.me/theorems/ac222a7f-46d9-4a8c-b1c7-6beb793ed5d7
-- title:
--   The running time of the detyped decider: dominated as soon as the typed sampler runs within (cS (W + 1)^{mS})^{K + 1} at degree eS (K + 1) at n, the cutoff routine…
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.DetypingDeciderCost` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The running time of the detyped decider. The detyped decider (`CL.Detyping.DeciderProgram.prog`) runs three stages on its input `(n, d)`: the typed sampler on the dimension query, the cutoff routine on `n`, and the router, which either answers directly or calls the typed decider once, on a typed input whose questions have the typed sampler's dimension and whose answers are within the inner cut (`route_call_typed`). So its time is dominated in the sense of `MIPRE.Pipeline.PDom` as soon as the three programs' are, the typed decider's on those inputs only (`prog_time`).
--
--   **The running time of the detyped decider**: dominated as soon as the typed sampler runs
--   within `(cS (W + 1)^{mS})^{K + 1}` at degree `eS (K + 1)` at `n`, the cutoff routine within a
--   dominated time, and the typed decider within one on the typed inputs the router hands it.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.CL
--   open MIPRE.CL.Detyping
--   open MIPRE.CL.Detyping.DeciderProgram
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun MIPRE.CL.Detyping.Program MIPRE.Pipeline
--   variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
--   variable (E : T → T → Prop) [DecidableRel E]
--   variable {ℓ : ℕ}
--
--   theorem MIPRE.CL.Detyping.DeciderProgram.prog_time (cS mS eS cC mC eC cD mD eD : ℕ) : ∃ c m e, ∀ {W K : ℕ}
--       (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram) (n : ℕ), n ≤ W →
--       S.TimeBoundAt n ((cS * (W + 1) ^ mS) ^ (K + 1)) (eS * (K + 1)) →
--       (∀ {X : ℕ}, 1 ≤ X → PRuns W X K cC mC eC C.prog (encode n) (encode (C.inner n, C.outer n))) →
--       (∀ {X : ℕ}, 1 ≤ X → ∀ (u v : T) (x y a b : BitStr), x.length = S.dim n →
--         y.length = S.dim n → a.length ≤ C.inner n → b.length ≤ C.inner n →
--         ∃ r, PRuns W X K cD mD eD D.prog (encode (n, u, x, v, y, a, b)) r) →
--       (decider E S D C).TimeBoundAt n ((c * (W + 1) ^ m) ^ (K + 1)) (e * (K + 1))
--   ```
--
--   **Formalization Note** `MIPRE.CL.Detyping.DeciderProgram.prog_time` is declared in `MIPRE/Foundations/CL/DetypingDeciderCost.lean`, lines 62–130. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingDeciderCost.lean#L62-L130; blueprint lem:ar-construction

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderProg
import Definitions.Def_MIPRE_Foundations_CL_DetypingDecider
import Definitions.Def_MIPRE_Foundations_Cost_While
import Definitions.Def_MIPRE_Foundations_Pipeline_UnaryArith
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDom
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDomRun

open MIPRE
open MIPRE.CL
open MIPRE.CL.Detyping
open MIPRE.CL.Detyping.DeciderProgram
open MIPRE.Cost MIPRE.Cost.PolyTimeFun MIPRE.CL.Detyping.Program MIPRE.Pipeline
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable (E : T → T → Prop) [DecidableRel E]
variable {ℓ : ℕ}

theorem MIPRE.CL.Detyping.DeciderProgram.prog_time (cS mS eS cC mC eC cD mD eD : ℕ) : ∃ c m e, ∀ {W K : ℕ}
    (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram) (n : ℕ), n ≤ W →
    S.TimeBoundAt n ((cS * (W + 1) ^ mS) ^ (K + 1)) (eS * (K + 1)) →
    (∀ {X : ℕ}, 1 ≤ X → PRuns W X K cC mC eC C.prog (encode n) (encode (C.inner n, C.outer n))) →
    (∀ {X : ℕ}, 1 ≤ X → ∀ (u v : T) (x y a b : BitStr), x.length = S.dim n →
      y.length = S.dim n → a.length ≤ C.inner n → b.length ≤ C.inner n →
      ∃ r, PRuns W X K cD mD eD D.prog (encode (n, u, x, v, y, a, b)) r) →
    (decider E S D C).TimeBoundAt n ((c * (W + 1) ^ m) ^ (K + 1)) (e * (K + 1)) := by sorry
