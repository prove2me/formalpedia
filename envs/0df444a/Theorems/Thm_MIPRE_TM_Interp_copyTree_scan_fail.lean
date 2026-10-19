-- Prove2me | Theorems.Thm_MIPRE_TM_Interp_copyTree_scan_fail
-- name    : MIPRE.TM.Interp.copyTree_scan_fail
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:19:39.559842+00:00
-- url     : https://prove2.me/theorems/1083e025-ee11-49a4-8a1d-ed615932e593
-- title:
--   The scan of the charged copy over S(v) with a budget r < |v| halts silently
-- statement:
--   A statement of the module `MIPRE.TM.Interp.CopyTreeCharge` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The charged `copyTree`. `copyTree src (some t) true` copies `S(v)` and pops one budget cell per bit: with a budget of at least `|v|` it succeeds (`exec_copyTree_charge`), otherwise it halts (`exec_copyTree_charge_fail`).
--
--   The scan of the charged copy over `S(v)` with a budget `r < |v|` halts silently.
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
--   theorem MIPRE.TM.Interp.copyTree_scan_fail {k : ProgId} {pc : Fin maxPc} {src t : WT}
--       (hins : instrAt k pc = .copyTree src (some t) true) (hpc : pc.val + 1 < maxPc)
--       (hst : src ≠ t) (hsc : src ≠ CNT) (htc : t ≠ CNT) (hsb : src ≠ BUD) (htb : t ≠ BUD) (v : Data) :
--       ∀ (c : Cfg input) (d r : ℕ), c.state = some ⟨k, pc, p1⟩ → 1 ≤ d →
--         Unary (c.workTapes CNT) d → c.workTapePos CNT = d →
--         Unary (c.workTapes BUD) r → c.workTapePos BUD = r → r < v.size →
--         Holds (c.workTapes src) (c.workTapePos src) (S v) →
--       HaltsIn c (4 * v.size)
--   ```
--
--   **Formalization Note** `MIPRE.TM.Interp.copyTree_scan_fail` is declared in `MIPRE/TM/Interp/CopyTreeCharge.lean`, lines 304–433. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/CopyTreeCharge.lean#L304-L433

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

theorem MIPRE.TM.Interp.copyTree_scan_fail {k : ProgId} {pc : Fin maxPc} {src t : WT}
    (hins : instrAt k pc = .copyTree src (some t) true) (hpc : pc.val + 1 < maxPc)
    (hst : src ≠ t) (hsc : src ≠ CNT) (htc : t ≠ CNT) (hsb : src ≠ BUD) (htb : t ≠ BUD) (v : Data) :
    ∀ (c : Cfg input) (d r : ℕ), c.state = some ⟨k, pc, p1⟩ → 1 ≤ d →
      Unary (c.workTapes CNT) d → c.workTapePos CNT = d →
      Unary (c.workTapes BUD) r → c.workTapePos BUD = r → r < v.size →
      Holds (c.workTapes src) (c.workTapePos src) (S v) →
    HaltsIn c (4 * v.size) := by sorry
