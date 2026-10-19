-- Prove2me | Theorems.Thm_MIPRE_TM_Interp_evDispatch_round
-- name    : MIPRE.TM.Interp.evDispatch_round
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:24:12.000073+00:00
-- url     : https://prove2.me/theorems/2e4741d6-f6a5-4c24-9cd0-6cba7cfef889
-- title:
--   One round of evDispatch: two moves and a branch on the bit two cells right
-- statement:
--   A statement of the module `MIPRE.TM.Interp.Step` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). One step of the evaluation machine. The representation of a configuration of the CEK machine on the tapes (`RepOf`), the dispatcher, and, for each case of `Machine.step`, the run of the case program from the representation of `m` to that of `step m`, charging `stepCost m` (`StepTo`), or halting silently when the budget is short.
--
--   One round of `evDispatch`: two moves and a branch on the bit two cells right.
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
--   theorem MIPRE.TM.Interp.evDispatch_round {pc : Fin maxPc} {tgt : ProgId} (h1 : instrAt .evDispatch pc = .move C true)
--       (h2 : pc.val + 1 < maxPc) (h2' : instrAt .evDispatch ⟨pc.val + 1, h2⟩ = .move C true)
--       (h3 : pc.val + 2 < maxPc) (h3' : instrAt .evDispatch ⟨pc.val + 2, h3⟩ = .branch C (some .zero) tgt)
--       {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .evDispatch pc) ds) :
--       ((ds C).l[(ds C).p + 2]? = some .zero →
--         ∃ c', Reach c 3 c' [] ∧ Desc c' (at_ tgt 0) (Function.update ds C ⟨(ds C).l, (ds C).p + 2⟩)) ∧
--       ((ds C).l[(ds C).p + 2]? ≠ some .zero → (h4 : pc.val + 2 + 1 < maxPc) →
--         ∃ c', Reach c 3 c' [] ∧
--           Desc c' (next_ .evDispatch ⟨pc.val + 2, h3⟩ h4)
--             (Function.update ds C ⟨(ds C).l, (ds C).p + 2⟩))
--   ```
--
--   **Formalization Note** `MIPRE.TM.Interp.evDispatch_round` is declared in `MIPRE/TM/Interp/Step.lean`, lines 223–244. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/Step.lean#L223-L244

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

theorem MIPRE.TM.Interp.evDispatch_round {pc : Fin maxPc} {tgt : ProgId} (h1 : instrAt .evDispatch pc = .move C true)
    (h2 : pc.val + 1 < maxPc) (h2' : instrAt .evDispatch ⟨pc.val + 1, h2⟩ = .move C true)
    (h3 : pc.val + 2 < maxPc) (h3' : instrAt .evDispatch ⟨pc.val + 2, h3⟩ = .branch C (some .zero) tgt)
    {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .evDispatch pc) ds) :
    ((ds C).l[(ds C).p + 2]? = some .zero →
      ∃ c', Reach c 3 c' [] ∧ Desc c' (at_ tgt 0) (Function.update ds C ⟨(ds C).l, (ds C).p + 2⟩)) ∧
    ((ds C).l[(ds C).p + 2]? ≠ some .zero → (h4 : pc.val + 2 + 1 < maxPc) →
      ∃ c', Reach c 3 c' [] ∧
        Desc c' (next_ .evDispatch ⟨pc.val + 2, h3⟩ h4)
          (Function.update ds C ⟨(ds C).l, (ds C).p + 2⟩)) := by sorry
