-- Prove2me | Theorems.Thm_MIPRE_CL_Detyping_DeciderProgram_numbered_clDist
-- name    : MIPRE.CL.Detyping.DeciderProgram.numbered_clDist
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:54:35.654584+00:00
-- url     : https://prove2.me/theorems/1a1b08a2-dfd3-4551-86e9-a4e5c8db325c
-- title:
--   The exact finite distribution obtained by numbering the detyped registers
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.DetypingDeciderTransport` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Same-state soundness for the actual detyped verifier. The actual sampler's numbered CL presentations have precisely the finite detyping distribution after the coordinate permutation. Together with the proved executable predicate law, this transports the existing finite-game restriction to strategies for the compiled ambient verifier.
--
--   The exact finite distribution obtained by numbering the detyped registers.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.CL
--   open MIPRE.CL.Detyping
--   open MIPRE.CL.Detyping.DeciderProgram
--   open MIPRE.Cost Finset
--   variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
--   variable {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
--   variable (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram)
--
--   theorem MIPRE.CL.Detyping.DeciderProgram.numbered_clDist (n : ℕ) (x y : Coord T (Fin (S.dim n)) → 𝔽₂) :
--       clDist (numbered E .alice (S.cl n .alice)).eval
--         (numbered E .bob (S.cl n .bob)).eval (vectorEquiv (S.dim n) x) (vectorEquiv (S.dim n) y) =
--       clDist (presentation E false (sourceFamily S n false)).eval
--         (presentation E true (sourceFamily S n true)).eval x y
--   ```
--
--   **Formalization Note** `MIPRE.CL.Detyping.DeciderProgram.numbered_clDist` is declared in `MIPRE/Foundations/CL/DetypingDeciderTransport.lean`, lines 40–62. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingDeciderTransport.lean#L40-L62; blueprint lem:detype-program-strategies

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic
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
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderRoute
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderProg
import Definitions.Def_MIPRE_Foundations_CL_DetypingDecider
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingCompleteSupport
import Definitions.Def_MIPRE_Foundations_CL_DetypingComplete
import Definitions.Def_MIPRE_Foundations_CL_DetypingDeciderTransport

open MIPRE
open MIPRE.CL
open MIPRE.CL.Detyping
open MIPRE.CL.Detyping.DeciderProgram
open MIPRE.Cost Finset
set_option linter.unusedSectionVars false
variable {T : Type*} [Fintype T] [DecidableEq T] [SizedEncoding T]
variable {ℓ : ℕ} (E : T → T → Prop) [DecidableRel E]
variable (S : TypedSampler ℓ T) (D : TypedDecider T) (C : CutoffProgram)

theorem MIPRE.CL.Detyping.DeciderProgram.numbered_clDist (n : ℕ) (x y : Coord T (Fin (S.dim n)) → 𝔽₂) :
    clDist (numbered E .alice (S.cl n .alice)).eval
      (numbered E .bob (S.cl n .bob)).eval (vectorEquiv (S.dim n) x) (vectorEquiv (S.dim n) y) =
    clDist (presentation E false (sourceFamily S n false)).eval
      (presentation E true (sourceFamily S n true)).eval x y := by sorry
