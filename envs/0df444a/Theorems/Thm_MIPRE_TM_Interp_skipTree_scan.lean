-- Prove2me | Theorems.Thm_MIPRE_TM_Interp_skipTree_scan
-- name    : MIPRE.TM.Interp.skipTree_scan
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:19:34.188976+00:00
-- url     : https://prove2.me/theorems/b43ff980-c8aa-440a-8e4a-774823a0bdfe
-- title:
--   The scan of copyTree src none false (a skip) over S(v) from d ≥ 1 pending subtrees
-- statement:
--   A statement of the module `MIPRE.TM.Interp.CopyTree` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The `copyTree` routine. Copying (or skipping) a preorder-serialized value: a scan with a unary counter of the pending subtrees on `CNT`, one more per `1` (a node with two children, itself consumed) and one fewer per `0` (a leaf), finishing when none is pending. The scan from `d ≥ 1` pending subtrees over `S(v)` leaves `d - 1` pending (`copyTree_scan`), finishing when `d = 1`; the instruction starts with one (`exec_copyTree`).
--
--   The scan of `copyTree src none false` (a skip) over `S(v)` from `d ≥ 1` pending
--   subtrees.
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
--   theorem MIPRE.TM.Interp.skipTree_scan {k : ProgId} {pc : Fin maxPc} {src : WT}
--       (hins : instrAt k pc = .copyTree src none false) (hpc : pc.val + 1 < maxPc)
--       (hsc : src ≠ CNT) (v : Data) :
--       ∀ (c : Cfg input) (d : ℕ), c.state = some ⟨k, pc, p1⟩ → 1 ≤ d →
--         Unary (c.workTapes CNT) d → c.workTapePos CNT = d →
--         Holds (c.workTapes src) (c.workTapePos src) (S v) →
--       ∃ n ≤ 3 * v.size, ∃ c', Reach c n c' [] ∧ c'.state = scanExit k pc hpc d ∧
--         Untouched c c' [] [src, CNT] ∧
--         c'.workTapes src = c.workTapes src ∧ c'.workTapePos src = c.workTapePos src + v.size ∧
--         Unary (c'.workTapes CNT) (d - 1) ∧ c'.workTapePos CNT = d - 1
--   ```
--
--   **Formalization Note** `MIPRE.TM.Interp.skipTree_scan` is declared in `MIPRE/TM/Interp/CopyTree.lean`, lines 234–360. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/CopyTree.lean#L234-L360

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

theorem MIPRE.TM.Interp.skipTree_scan {k : ProgId} {pc : Fin maxPc} {src : WT}
    (hins : instrAt k pc = .copyTree src none false) (hpc : pc.val + 1 < maxPc)
    (hsc : src ≠ CNT) (v : Data) :
    ∀ (c : Cfg input) (d : ℕ), c.state = some ⟨k, pc, p1⟩ → 1 ≤ d →
      Unary (c.workTapes CNT) d → c.workTapePos CNT = d →
      Holds (c.workTapes src) (c.workTapePos src) (S v) →
    ∃ n ≤ 3 * v.size, ∃ c', Reach c n c' [] ∧ c'.state = scanExit k pc hpc d ∧
      Untouched c c' [] [src, CNT] ∧
      c'.workTapes src = c.workTapes src ∧ c'.workTapePos src = c.workTapePos src + v.size ∧
      Unary (c'.workTapes CNT) (d - 1) ∧ c'.workTapePos CNT = d - 1 := by sorry
