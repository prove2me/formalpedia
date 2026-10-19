-- Prove2me | Theorems.Thm_MIPRE_TM_Interp_exec_charge_one
-- name    : MIPRE.TM.Interp.exec_charge_one
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:23:48.727121+00:00
-- url     : https://prove2.me/theorems/00042919-e24d-4921-b781-3bff8157d6fd
-- title:
--   charge: one step left, then a pop per unit; halts on an exhausted budget
-- statement:
--   A statement of the module `MIPRE.TM.Interp.Routines` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The routines: specifications of the instructions. Each instruction's specification is a reachability statement: from a configuration at the instruction's first phase, with the tapes it reads in a stated shape, a bounded number of steps leads to the configuration at the next instruction, with the stated effect on the tapes it touches and none on the others (`Untouched`).
--
--   `charge`: one step left, then a pop per unit; halts on an exhausted budget.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.TM
--   open MIPRE.TM.Interp
--   open Turing MultiInputTM Phase
--   open MultiTapeTM (moveInputPos)
--   variable {input : Fin 7 → List Sym}
--
--   theorem MIPRE.TM.Interp.exec_charge_one {k : ProgId} {pc : Fin maxPc}
--       (hins : instrAt k pc = .charge false) (hpc : pc.val + 1 < maxPc) (c : Cfg input)
--       (hq : c.state = at_ k pc) {r : ℕ} (hb : Unary (c.workTapes BUD) (r + 1))
--       (hpos : c.workTapePos BUD = r + 1) :
--       ∃ c', Reach c 2 c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [BUD] ∧
--         Unary (c'.workTapes BUD) r ∧ c'.workTapePos BUD = r
--   ```
--
--   **Formalization Note** `MIPRE.TM.Interp.exec_charge_one` is declared in `MIPRE/TM/Interp/Routines.lean`, lines 901–930. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/Routines.lean#L901-L930

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Computability.Language
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_Interp_Tape
import Definitions.Def_MIPRE_TM_Interp_Reach
import Definitions.Def_MIPRE_TM_Interp_Routines

open MIPRE
open MIPRE.TM
open MIPRE.TM.Interp
open Turing MultiInputTM Phase
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}

theorem MIPRE.TM.Interp.exec_charge_one {k : ProgId} {pc : Fin maxPc}
    (hins : instrAt k pc = .charge false) (hpc : pc.val + 1 < maxPc) (c : Cfg input)
    (hq : c.state = at_ k pc) {r : ℕ} (hb : Unary (c.workTapes BUD) (r + 1))
    (hpos : c.workTapePos BUD = r + 1) :
    ∃ c', Reach c 2 c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [BUD] ∧
      Unary (c'.workTapes BUD) r ∧ c'.workTapePos BUD = r := by sorry
