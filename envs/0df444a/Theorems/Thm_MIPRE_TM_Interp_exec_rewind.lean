-- Prove2me | Theorems.Thm_MIPRE_TM_Interp_exec_rewind
-- name    : MIPRE.TM.Interp.exec_rewind
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:22:50.87498+00:00
-- url     : https://prove2.me/theorems/5a56c1a6-63ba-4120-8e50-eb465685b9da
-- title:
--   From cell p + n with cells p … p + n - 1 not blank and p - 1 blank, rewind reaches cell p (the head may start on the blank after the content)
-- statement:
--   A statement of the module `MIPRE.TM.Interp.Routines` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The routines: specifications of the instructions. Each instruction's specification is a reachability statement: from a configuration at the instruction's first phase, with the tapes it reads in a stated shape, a bounded number of steps leads to the configuration at the next instruction, with the stated effect on the tapes it touches and none on the others (`Untouched`).
--
--   From cell `p + n` with cells `p … p + n - 1` not blank and `p - 1` blank, `rewind`
--   reaches cell `p` (the head may start on the blank after the content).
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
--   theorem MIPRE.TM.Interp.exec_rewind {k : ProgId} {pc : Fin maxPc} {t : WT}
--       (hins : instrAt k pc = .rewind t) (hpc : pc.val + 1 < maxPc) (n : ℕ)
--       (c : Cfg input) (hq : c.state = at_ k pc)
--       (hne : ∀ q, c.workTapePos t - n ≤ q → q < c.workTapePos t → c.workTapes t q ≠ none)
--       (hbl : c.workTapes t (c.workTapePos t - n - 1) = none) :
--       ∃ c', Reach c (n + 2) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [t] ∧
--         c'.workTapes t = c.workTapes t ∧ c'.workTapePos t = c.workTapePos t - n
--   ```
--
--   **Formalization Note** `MIPRE.TM.Interp.exec_rewind` is declared in `MIPRE/TM/Interp/Routines.lean`, lines 246–276. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/Routines.lean#L246-L276

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

theorem MIPRE.TM.Interp.exec_rewind {k : ProgId} {pc : Fin maxPc} {t : WT}
    (hins : instrAt k pc = .rewind t) (hpc : pc.val + 1 < maxPc) (n : ℕ)
    (c : Cfg input) (hq : c.state = at_ k pc)
    (hne : ∀ q, c.workTapePos t - n ≤ q → q < c.workTapePos t → c.workTapes t q ≠ none)
    (hbl : c.workTapes t (c.workTapePos t - n - 1) = none) :
    ∃ c', Reach c (n + 2) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [t] ∧
      c'.workTapes t = c.workTapes t ∧ c'.workTapePos t = c.workTapePos t - n := by sorry
