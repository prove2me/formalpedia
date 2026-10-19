-- Prove2me | Theorems.Thm_MIPRE_TM_Interp_case_evCons
-- name    : MIPRE.TM.Interp.case_evCons
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:24:49.588484+00:00
-- url     : https://prove2.me/theorems/5e40839a-5a3b-444c-b509-eb8ece03b647
-- title:
--   The common tail of evCons and evLet: after the frame is pushed, rebuild the control from the scratch tape and charge
-- statement:
--   A statement of the module `MIPRE.TM.Interp.Step` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). One step of the evaluation machine. The representation of a configuration of the CEK machine on the tapes (`RepOf`), the dispatcher, and, for each case of `Machine.step`, the run of the case program from the representation of `m` to that of `step m`, charging `stepCost m` (`StepTo`), or halting silently when the budget is short.
--
--   The common tail of `evCons` and `evLet`: after the frame is pushed, rebuild the control
--   from the scratch tape and charge. Stated inline in each case.
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
--   theorem MIPRE.TM.Interp.case_evCons {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .evCons 0) ds)
--       {h t : Prog} {env : Env} {k : List Frame} {r : ℕ}
--       (hr : RepOf ds ⟨.ev (.cons h t), env, k⟩ r 6 (kontRepr k).length) :
--       PreTo c (caseBound ⟨.ev (.cons h t), env, k⟩ (ds X).l.length) (at_ .evCons 15)
--         ⟨.ev h, env, .cons1 t env :: k⟩ r (ctrlRepr (.ev h)).length
--         (kontRepr (.cons1 t env :: k)).length ((ds X).l.length + sz ⟨.ev (.cons h t), env, k⟩)
--   ```
--
--   **Formalization Note** `MIPRE.TM.Interp.case_evCons` is declared in `MIPRE/TM/Interp/Step.lean`, lines 592–657. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/Step.lean#L592-L657

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

theorem MIPRE.TM.Interp.case_evCons {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .evCons 0) ds)
    {h t : Prog} {env : Env} {k : List Frame} {r : ℕ}
    (hr : RepOf ds ⟨.ev (.cons h t), env, k⟩ r 6 (kontRepr k).length) :
    PreTo c (caseBound ⟨.ev (.cons h t), env, k⟩ (ds X).l.length) (at_ .evCons 15)
      ⟨.ev h, env, .cons1 t env :: k⟩ r (ctrlRepr (.ev h)).length
      (kontRepr (.cons1 t env :: k)).length ((ds X).l.length + sz ⟨.ev (.cons h t), env, k⟩) := by sorry
