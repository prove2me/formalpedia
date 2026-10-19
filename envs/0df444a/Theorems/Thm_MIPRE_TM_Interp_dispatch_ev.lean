-- Prove2me | Theorems.Thm_MIPRE_TM_Interp_dispatch_ev
-- name    : MIPRE.TM.Interp.dispatch_ev
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:25:00.753128+00:00
-- url     : https://prove2.me/theorems/ca7262e4-6a27-4954-93b5-679747dae8f5
-- title:
--   From the dispatcher, a control ev p reaches its case program with the head of C on the final 0 of the tag
-- statement:
--   A statement of the module `MIPRE.TM.Interp.Step` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). One step of the evaluation machine. The representation of a configuration of the CEK machine on the tapes (`RepOf`), the dispatcher, and, for each case of `Machine.step`, the run of the case program from the representation of `m` to that of `step m`, charging `stepCost m` (`StepTo`), or halting silently when the budget is short.
--
--   From the dispatcher, a control `ev p` reaches its case program with the head of `C` on the
--   final `0` of the tag.
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
--   theorem MIPRE.TM.Interp.dispatch_ev {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .dispatch 0) ds)
--       {p : Prog} {env : Env} {k : List Frame} {r : ℕ}
--       (hr : RepOf ds ⟨.ev p, env, k⟩ r (ctrlRepr (.ev p)).length (kontRepr k).length) :
--       PreTo1 c ((ctrlRepr (.ev p)).length + 26) (at_ (evTarget p) 0) ⟨.ev p, env, k⟩ r (evHead p)
--         (kontRepr k).length (ds X).l.length
--   ```
--
--   **Formalization Note** `MIPRE.TM.Interp.dispatch_ev` is declared in `MIPRE/TM/Interp/Step.lean`, lines 265–382. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/Step.lean#L265-L382

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

theorem MIPRE.TM.Interp.dispatch_ev {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .dispatch 0) ds)
    {p : Prog} {env : Env} {k : List Frame} {r : ℕ}
    (hr : RepOf ds ⟨.ev p, env, k⟩ r (ctrlRepr (.ev p)).length (kontRepr k).length) :
    PreTo1 c ((ctrlRepr (.ev p)).length + 26) (at_ (evTarget p) 0) ⟨.ev p, env, k⟩ r (evHead p)
      (kontRepr k).length (ds X).l.length := by sorry
