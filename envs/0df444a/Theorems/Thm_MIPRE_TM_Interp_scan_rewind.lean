-- Prove2me | Theorems.Thm_MIPRE_TM_Interp_scan_rewind
-- name    : MIPRE.TM.Interp.scan_rewind
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:22:50.614989+00:00
-- url     : https://prove2.me/theorems/483cf6eb-d1f8-4bc0-80c4-fa3d151609b7
-- title:
--   The scan of rewind from p1: cells pos - n + 1 … pos not blank, pos - n blank
-- statement:
--   A statement of the module `MIPRE.TM.Interp.Routines` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The routines: specifications of the instructions. Each instruction's specification is a reachability statement: from a configuration at the instruction's first phase, with the tapes it reads in a stated shape, a bounded number of steps leads to the configuration at the next instruction, with the stated effect on the tapes it touches and none on the others (`Untouched`).
--
--   The scan of `rewind` from `p1`: cells `pos - n + 1 … pos` not blank, `pos - n` blank.
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
--   theorem MIPRE.TM.Interp.scan_rewind {k : ProgId} {pc : Fin maxPc} {t : WT}
--       (hins : instrAt k pc = .rewind t) (hpc : pc.val + 1 < maxPc) (n : ℕ) :
--       ∀ (c : Cfg input), c.state = some ⟨k, pc, p1⟩ →
--         (∀ q, c.workTapePos t - n < q → q ≤ c.workTapePos t → c.workTapes t q ≠ none) →
--         c.workTapes t (c.workTapePos t - n) = none →
--       ∃ c', Reach c (n + 1) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [t] ∧
--         c'.workTapes t = c.workTapes t ∧ c'.workTapePos t = c.workTapePos t - n + 1
--   ```
--
--   **Formalization Note** `MIPRE.TM.Interp.scan_rewind` is declared in `MIPRE/TM/Interp/Routines.lean`, lines 195–244. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/Routines.lean#L195-L244

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

theorem MIPRE.TM.Interp.scan_rewind {k : ProgId} {pc : Fin maxPc} {t : WT}
    (hins : instrAt k pc = .rewind t) (hpc : pc.val + 1 < maxPc) (n : ℕ) :
    ∀ (c : Cfg input), c.state = some ⟨k, pc, p1⟩ →
      (∀ q, c.workTapePos t - n < q → q ≤ c.workTapePos t → c.workTapes t q ≠ none) →
      c.workTapes t (c.workTapePos t - n) = none →
    ∃ c', Reach c (n + 1) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [t] ∧
      c'.workTapes t = c.workTapes t ∧ c'.workTapePos t = c.workTapePos t - n + 1 := by sorry
