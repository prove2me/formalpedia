-- Prove2me | Theorems.Thm_MIPRE_Repeat_DecAcc_iff
-- name    : MIPRE.Repeat.DecAcc_iff
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:46:13.39962+00:00
-- url     : https://prove2.me/theorems/ab3fad04-923b-4721-a156-323f20c49835
-- title:
--   The acceptance predicate of the coordinate loop, read as k-tuples of bit strings
-- statement:
--   A statement of the module `MIPRE.Foundations.Repeat.RepDecider` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The repeated decider. The decider of `ComputeParrepVerifier` (`thm:parallel-repetition`) as a `Decider`: the core `Prog.repDecCore` of `MIPRE.Foundations.Repeat.DecMain`, run through the self-interpreter and the s-m-n construction on `((S̄, D̄), λ, τ, β)`. Its acceptance is characterized exactly (`repDecider_accepts_iff`): on `(n, x, y, a, b)` it accepts iff `|x| = |y| = k s`, `a` and `b` are the serializations of lists of `k` bit strings of length at most `B` each, and the input decider accepts every coordinate `(n, x_i, y_i, a_i, b_i)`, with `k = 2^{τ(|λ| + |n|)}`, `s = s(n)` the dimension…
--
--   The acceptance predicate of the coordinate loop, read as `k`-tuples of bit strings.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Repeat
--   open MIPRE.Cost MIPRE.Cost.Data MIPRE.Cost.Prog MIPRE.CL
--   variable {ℓ : ℕ} (S : CL.Sampler ℓ) (D : Decider)
--
--   theorem MIPRE.Repeat.DecAcc_iff (univ : Prog) (dD nD : Data) (s B : ℕ) :
--       ∀ (k : ℕ) (remX remY remA remB : List Data),
--         DecAcc univ dD nD s B k remX remY remA remB ↔
--           ∃ aa bb : Fin k → BitStr,
--             remA = List.ofFn (fun i => encode (aa i)) ∧ remB = List.ofFn (fun i => encode (bb i)) ∧
--             ∀ i, (aa i).length ≤ B ∧ (bb i).length ≤ B ∧
--               ∃ t, Eval [decQuery dD nD (list (chunk s i remX)) (list (chunk s i remY))
--                 (encode (aa i)) (encode (bb i))] univ (.cons .nil .nil) t
--   ```
--
--   **Formalization Note** `MIPRE.Repeat.DecAcc_iff` is declared in `MIPRE/Foundations/Repeat/RepDecider.lean`, lines 77–124. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Repeat/RepDecider.lean#L77-L124

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_Pipeline_Repetition
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_Repeat_MapLoop
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Repeat_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Repeat_RepSampler
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Repeat_DecLoop
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Repeat_DecMain
import Definitions.Def_MIPRE_Foundations_Repeat_RepDecider

open MIPRE
open MIPRE.Repeat
open MIPRE.Cost MIPRE.Cost.Data MIPRE.Cost.Prog MIPRE.CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (D : Decider)

theorem MIPRE.Repeat.DecAcc_iff (univ : Prog) (dD nD : Data) (s B : ℕ) :
    ∀ (k : ℕ) (remX remY remA remB : List Data),
      DecAcc univ dD nD s B k remX remY remA remB ↔
        ∃ aa bb : Fin k → BitStr,
          remA = List.ofFn (fun i => encode (aa i)) ∧ remB = List.ofFn (fun i => encode (bb i)) ∧
          ∀ i, (aa i).length ≤ B ∧ (bb i).length ≤ B ∧
            ∃ t, Eval [decQuery dD nD (list (chunk s i remX)) (list (chunk s i remY))
              (encode (aa i)) (encode (bb i))] univ (.cons .nil .nil) t := by sorry
