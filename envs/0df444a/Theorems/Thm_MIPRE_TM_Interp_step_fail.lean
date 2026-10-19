-- Prove2me | Theorems.Thm_MIPRE_TM_Interp_step_fail
-- name    : MIPRE.TM.Interp.step_fail
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:25:35.513312+00:00
-- url     : https://prove2.me/theorems/836f229a-8968-46ed-9da0-8f6ea850e189
-- title:
--   One step of the machine, when the budget is short: U halts silently
-- statement:
--   A statement of the module `MIPRE.TM.Interp.Step` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). One step of the evaluation machine. The representation of a configuration of the CEK machine on the tapes (`RepOf`), the dispatcher, and, for each case of `Machine.step`, the run of the case program from the representation of `m` to that of `step m`, charging `stepCost m` (`StepTo`), or halting silently when the budget is short.
--
--   **One step of the machine**, when the budget is short: `U` halts silently.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.TM
--   open MIPRE.TM.Interp
--   open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
--   variable {input : Fin 7 → List Sym}
--
--   theorem MIPRE.TM.Interp.step_fail {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .dispatch 0) ds)
--       {m : Machine.Cfg} {r : ℕ}
--       (hr : RepOf ds m r (ctrlRepr m.ctrl).length (kontRepr m.kont).length)
--       (hnf : ∀ v, m.ctrl = .ret v → m.kont ≠ []) (hcost : r < stepCost m) :
--       HaltsIn c (stepBound m (ds X).l.length)
--   ```
--
--   **Formalization Note** `MIPRE.TM.Interp.step_fail` is declared in `MIPRE/TM/Interp/Step.lean`, lines 1948–2016. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/Step.lean#L1948-L2016

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Language
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_Interp_Tape
import Definitions.Def_MIPRE_TM_Interp_Reach
import Definitions.Def_MIPRE_TM_Interp_Routines
import Definitions.Def_MIPRE_TM_Interp_Repr
import Definitions.Def_MIPRE_TM_Interp_CopyTree
import Definitions.Def_MIPRE_TM_Interp_GetEnv
import Definitions.Def_MIPRE_TM_Interp_Desc
import Definitions.Def_MIPRE_TM_Interp_Step

open MIPRE
open MIPRE.TM
open MIPRE.TM.Interp
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}

theorem MIPRE.TM.Interp.step_fail {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .dispatch 0) ds)
    {m : Machine.Cfg} {r : ℕ}
    (hr : RepOf ds m r (ctrlRepr m.ctrl).length (kontRepr m.kont).length)
    (hnf : ∀ v, m.ctrl = .ret v → m.kont ≠ []) (hcost : r < stepCost m) :
    HaltsIn c (stepBound m (ds X).l.length) := by sorry
