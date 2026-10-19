-- Prove2me | Theorems.Thm_MIPRE_TM_Interp_scan_eraseBack
-- name    : MIPRE.TM.Interp.scan_eraseBack
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:23:00.427724+00:00
-- url     : https://prove2.me/theorems/3be82b40-6a9c-413d-a947-49821556d257
-- title:
--   The return scan of eraseRight (p2): back over n blanks to the $, erase it
-- statement:
--   A statement of the module `MIPRE.TM.Interp.Routines` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The routines: specifications of the instructions. Each instruction's specification is a reachability statement: from a configuration at the instruction's first phase, with the tapes it reads in a stated shape, a bounded number of steps leads to the configuration at the next instruction, with the stated effect on the tapes it touches and none on the others (`Untouched`).
--
--   The return scan of `eraseRight` (`p2`): back over `n` blanks to the `$`, erase it.
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
--   theorem MIPRE.TM.Interp.scan_eraseBack {k : ProgId} {pc : Fin maxPc} {t : WT}
--       (hins : instrAt k pc = .eraseRight t) (hpc : pc.val + 1 < maxPc) (n : ℕ) :
--       ∀ (c : Cfg input), c.state = some ⟨k, pc, p2⟩ →
--         BlankFrom (c.workTapes t) (c.workTapePos t - n + 1) n →
--         c.workTapes t (c.workTapePos t - n) = some .fr →
--       ∃ c', Reach c (n + 1) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [t] ∧
--         c'.workTapes t = Function.update (c.workTapes t) (c.workTapePos t - n) none ∧
--         c'.workTapePos t = c.workTapePos t - n
--   ```
--
--   **Formalization Note** `MIPRE.TM.Interp.scan_eraseBack` is declared in `MIPRE/TM/Interp/Routines.lean`, lines 342–393. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/Routines.lean#L342-L393

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

theorem MIPRE.TM.Interp.scan_eraseBack {k : ProgId} {pc : Fin maxPc} {t : WT}
    (hins : instrAt k pc = .eraseRight t) (hpc : pc.val + 1 < maxPc) (n : ℕ) :
    ∀ (c : Cfg input), c.state = some ⟨k, pc, p2⟩ →
      BlankFrom (c.workTapes t) (c.workTapePos t - n + 1) n →
      c.workTapes t (c.workTapePos t - n) = some .fr →
    ∃ c', Reach c (n + 1) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [t] ∧
      c'.workTapes t = Function.update (c.workTapes t) (c.workTapePos t - n) none ∧
      c'.workTapePos t = c.workTapePos t - n := by sorry
