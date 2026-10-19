-- Prove2me | Theorems.Thm_MIPRE_TM_CookLevin_Desc_sat_tableau_of_sat_formula3
-- name    : MIPRE.TM.CookLevin.Desc.sat_tableau_of_sat_formula3
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:15:37.547315+00:00
-- url     : https://prove2.me/theorems/1a8c4197-9e0d-4eda-91f5-5b07ec32c1a4
-- title:
--   From an assignment of the described formula to a tableau assignment
-- statement:
--   A statement of the module `MIPRE.TM.CookLevin.Sat` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The described formula and the answers. The two halves of item 1 of `thm:succinct-sat` for the describer: a satisfying assignment of the described formula extending the two answer blocks exists iff the blocks are the two-bit tape encodings (`tapeBits`) of strings of length at most `T` that the decider accepts within `T` (`planning/succinct-cook-levin.md`, S3). The bridge in both directions is the decoding: an assignment of the formula gives the tableau assignment `w ∘ idxOf` (`sat_tableau_of_sat_formula3`), and an assignment of the tableau gives the formula assignment `decodeVar · |>.elim…
--
--   **From an assignment of the described formula to a tableau assignment.**
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.TM
--   open MIPRE.TM.CookLevin
--   open MIPRE.TM.CookLevin.Desc
--   open MIPRE.TM.Interp MIPRE.SAT MIPRE.Cost Fml
--   variable (e T : ℕ) (D : Prog) (n : ℕ) (x y : BitStr)
--
--   theorem MIPRE.TM.CookLevin.Desc.sat_tableau_of_sat_formula3 (hT : T ≤ Sof e) (hlen : FixedLen e D n T x y)
--       (hTm : T + 3 < 2 ^ W e) (w : Fin (2 ^ mOf e Gc) → Bool)
--       (hw : ((descCirc e T D n x y).formula3 (mOf e Gc)).Sat w) :
--       (tableauPlus e T (fixedOf D n T x y) chk).Sat
--         fun v => w ⟨idxOf e Gc T v, idxOf_lt e Gc T hT v⟩
--   ```
--
--   **Formalization Note** `MIPRE.TM.CookLevin.Desc.sat_tableau_of_sat_formula3` is declared in `MIPRE/TM/CookLevin/Sat.lean`, lines 120–143. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Sat.lean#L120-L143

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Language
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_CookLevin_Layout
import Definitions.Def_MIPRE_TM_CookLevin_FieldFml
import Definitions.Def_MIPRE_TM_CookLevin_Kinds
import Definitions.Def_MIPRE_TM_CookLevin_Families
import Definitions.Def_MIPRE_TM_CookLevin_Window
import Definitions.Def_MIPRE_TM_CookLevin_FamilyFml
import Definitions.Def_MIPRE_TM_Interp_Tape
import Definitions.Def_MIPRE_TM_Interp_Reach
import Definitions.Def_MIPRE_TM_Interp_Routines
import Definitions.Def_MIPRE_TM_Interp_Repr
import Definitions.Def_MIPRE_TM_Interp_CopyTree
import Definitions.Def_MIPRE_TM_Interp_GetEnv
import Definitions.Def_MIPRE_TM_Interp_Desc
import Definitions.Def_MIPRE_TM_Interp_Step
import Definitions.Def_MIPRE_TM_Interp_InputRoutines
import Definitions.Def_MIPRE_TM_Interp_Run
import Definitions.Def_MIPRE_Foundations_SAT_Table
import Definitions.Def_MIPRE_TM_CookLevin_Params
import Definitions.Def_MIPRE_TM_CookLevin_AnsEnd
import Definitions.Def_MIPRE_TM_CookLevin_Index
import Definitions.Def_MIPRE_TM_CookLevin_Describer
import Definitions.Def_MIPRE_TM_CookLevin_Semantics
import Definitions.Def_MIPRE_TM_CookLevin_Correct
import Definitions.Def_MIPRE_TM_CookLevin_Sound
import Definitions.Def_MIPRE_TM_CookLevin_Sat

open MIPRE
open MIPRE.TM
open MIPRE.TM.CookLevin
open MIPRE.TM.CookLevin.Desc
open MIPRE.TM.Interp MIPRE.SAT MIPRE.Cost Fml
variable (e T : ℕ) (D : Prog) (n : ℕ) (x y : BitStr)

theorem MIPRE.TM.CookLevin.Desc.sat_tableau_of_sat_formula3 (hT : T ≤ Sof e) (hlen : FixedLen e D n T x y)
    (hTm : T + 3 < 2 ^ W e) (w : Fin (2 ^ mOf e Gc) → Bool)
    (hw : ((descCirc e T D n x y).formula3 (mOf e Gc)).Sat w) :
    (tableauPlus e T (fixedOf D n T x y) chk).Sat
      fun v => w ⟨idxOf e Gc T v, idxOf_lt e Gc T hT v⟩ := by sorry
