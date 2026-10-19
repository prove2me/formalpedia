-- Prove2me | Theorems.Thm_MIPRE_TM_Interp_final_run
-- name    : MIPRE.TM.Interp.final_run
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:25:41.170829+00:00
-- url     : https://prove2.me/theorems/7dc5c7cf-7717-4da2-8526-3c531a8c9927
-- title:
--   The final check on ret v with an empty stack: accept iff v = encode true
-- statement:
--   A statement of the module `MIPRE.TM.Interp.Step` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). One step of the evaluation machine. The representation of a configuration of the CEK machine on the tapes (`RepOf`), the dispatcher, and, for each case of `Machine.step`, the run of the case program from the representation of `m` to that of `step m`, charging `stepCost m` (`StepTo`), or halting silently when the budget is short.
--
--   The final check on `ret v` with an empty stack: accept iff `v = encode true`.
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
--   theorem MIPRE.TM.Interp.final_run {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .dispatch 0) ds)
--       {v : Data} {env : Env} {r : ℕ}
--       (hr : RepOf ds ⟨.ret v, env, []⟩ r (ctrlRepr (.ret v)).length (kontRepr []).length) :
--       (v = Data.ofBool true → ∃ n ≤ v.size + 16, AcceptsFrom c n) ∧
--       (v ≠ Data.ofBool true → HaltsIn c (v.size + 16))
--   ```
--
--   **Formalization Note** `MIPRE.TM.Interp.final_run` is declared in `MIPRE/TM/Interp/Step.lean`, lines 1758–1824. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/Step.lean#L1758-L1824

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

theorem MIPRE.TM.Interp.final_run {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .dispatch 0) ds)
    {v : Data} {env : Env} {r : ℕ}
    (hr : RepOf ds ⟨.ret v, env, []⟩ r (ctrlRepr (.ret v)).length (kontRepr []).length) :
    (v = Data.ofBool true → ∃ n ≤ v.size + 16, AcceptsFrom c n) ∧
    (v ≠ Data.ofBool true → HaltsIn c (v.size + 16)) := by sorry
