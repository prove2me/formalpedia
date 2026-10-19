-- Prove2me | Theorems.Thm_MIPRE_TM_Interp_exec_copyTree_charge
-- name    : MIPRE.TM.Interp.exec_copyTree_charge
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:19:44.722987+00:00
-- url     : https://prove2.me/theorems/e9192078-7ea8-4bcb-b320-d244db91b48b
-- title:
--   copyTree src (some t) true with a sufficient budget
-- statement:
--   A statement of the module `MIPRE.TM.Interp.CopyTreeCharge` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The charged `copyTree`. `copyTree src (some t) true` copies `S(v)` and pops one budget cell per bit: with a budget of at least `|v|` it succeeds (`exec_copyTree_charge`), otherwise it halts (`exec_copyTree_charge_fail`).
--
--   **`copyTree src (some t) true`** with a sufficient budget.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.TM
--   open MIPRE.TM.Interp
--   open Turing MultiInputTM Phase MIPRE.Cost
--   variable {input : Fin 7 → List Sym}
--
--   theorem MIPRE.TM.Interp.exec_copyTree_charge {k : ProgId} {pc : Fin maxPc} {src t : WT}
--       (hins : instrAt k pc = .copyTree src (some t) true) (hpc : pc.val + 1 < maxPc)
--       (hst : src ≠ t) (hsc : src ≠ CNT) (htc : t ≠ CNT) (hsb : src ≠ BUD) (htb : t ≠ BUD) (v : Data)
--       (c : Cfg input) (hq : c.state = at_ k pc) (hcnt : Unary (c.workTapes CNT) 0)
--       (hcp : c.workTapePos CNT = 0) {r : ℕ} (hbud : Unary (c.workTapes BUD) r)
--       (hbp : c.workTapePos BUD = r) (hr : v.size ≤ r)
--       (hsrc : Holds (c.workTapes src) (c.workTapePos src) (S v)) :
--       ∃ n ≤ 4 * v.size + 1, ∃ c', Reach c n c' [] ∧ c'.state = next_ k pc hpc ∧
--         Untouched c c' [] [src, CNT, t, BUD] ∧
--         c'.workTapes src = c.workTapes src ∧ c'.workTapePos src = c.workTapePos src + v.size ∧
--         Unary (c'.workTapes CNT) 0 ∧ c'.workTapePos CNT = 0 ∧
--         Unary (c'.workTapes BUD) (r - v.size) ∧ c'.workTapePos BUD = ((r - v.size : ℕ) : ℤ) ∧
--         DstEff t c c' (S v)
--   ```
--
--   **Formalization Note** `MIPRE.TM.Interp.exec_copyTree_charge` is declared in `MIPRE/TM/Interp/CopyTreeCharge.lean`, lines 270–301. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/CopyTreeCharge.lean#L270-L301

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

open MIPRE
open MIPRE.TM
open MIPRE.TM.Interp
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}

theorem MIPRE.TM.Interp.exec_copyTree_charge {k : ProgId} {pc : Fin maxPc} {src t : WT}
    (hins : instrAt k pc = .copyTree src (some t) true) (hpc : pc.val + 1 < maxPc)
    (hst : src ≠ t) (hsc : src ≠ CNT) (htc : t ≠ CNT) (hsb : src ≠ BUD) (htb : t ≠ BUD) (v : Data)
    (c : Cfg input) (hq : c.state = at_ k pc) (hcnt : Unary (c.workTapes CNT) 0)
    (hcp : c.workTapePos CNT = 0) {r : ℕ} (hbud : Unary (c.workTapes BUD) r)
    (hbp : c.workTapePos BUD = r) (hr : v.size ≤ r)
    (hsrc : Holds (c.workTapes src) (c.workTapePos src) (S v)) :
    ∃ n ≤ 4 * v.size + 1, ∃ c', Reach c n c' [] ∧ c'.state = next_ k pc hpc ∧
      Untouched c c' [] [src, CNT, t, BUD] ∧
      c'.workTapes src = c.workTapes src ∧ c'.workTapePos src = c.workTapePos src + v.size ∧
      Unary (c'.workTapes CNT) 0 ∧ c'.workTapePos CNT = 0 ∧
      Unary (c'.workTapes BUD) (r - v.size) ∧ c'.workTapePos BUD = ((r - v.size : ℕ) : ℤ) ∧
      DstEff t c c' (S v) := by sorry
