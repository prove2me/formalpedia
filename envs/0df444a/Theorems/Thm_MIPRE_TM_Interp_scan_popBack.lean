-- Prove2me | Theorems.Thm_MIPRE_TM_Interp_scan_popBack
-- name    : MIPRE.TM.Interp.scan_popBack
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:22:59.012969+00:00
-- url     : https://prove2.me/theorems/1c79b618-5a17-49ff-9135-621a8eaee449
-- title:
--   The scan of popBack (phase p2): erase the cells pos - n + 1 … pos, none holding m, to the marker or blank at pos - n, then one right
-- statement:
--   A statement of the module `MIPRE.TM.Interp.Routines` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The routines: specifications of the instructions. Each instruction's specification is a reachability statement: from a configuration at the instruction's first phase, with the tapes it reads in a stated shape, a bounded number of steps leads to the configuration at the next instruction, with the stated effect on the tapes it touches and none on the others (`Untouched`).
--
--   The scan of `popBack` (phase `p2`): erase the cells `pos - n + 1 … pos`, none holding `m`,
--   to the marker or blank at `pos - n`, then one right.
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
--   theorem MIPRE.TM.Interp.scan_popBack {k : ProgId} {pc : Fin maxPc} {m : Sym} {t : WT}
--       (hins : instrAt k pc = .popBack m t) (hpc : pc.val + 1 < maxPc) (l : List Sym) :
--       ∀ (c : Cfg input), c.state = some ⟨k, pc, p2⟩ →
--         Holds (c.workTapes t) (c.workTapePos t + 1 - l.length) l → (∀ s ∈ l, s ≠ m) →
--         (c.workTapes t (c.workTapePos t - l.length) = some m ∨
--           c.workTapes t (c.workTapePos t - l.length) = none) →
--       ∃ c', Reach c (l.length + 1) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [t] ∧
--         (∀ q, (q < c.workTapePos t + 1 - l.length ∨ c.workTapePos t < q) →
--           c'.workTapes t q = c.workTapes t q) ∧
--         BlankFrom (c'.workTapes t) (c.workTapePos t + 1 - l.length) l.length ∧
--         c'.workTapePos t = c.workTapePos t - l.length + 1
--   ```
--
--   **Formalization Note** `MIPRE.TM.Interp.scan_popBack` is declared in `MIPRE/TM/Interp/Routines.lean`, lines 685–765. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/Routines.lean#L685-L765

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

theorem MIPRE.TM.Interp.scan_popBack {k : ProgId} {pc : Fin maxPc} {m : Sym} {t : WT}
    (hins : instrAt k pc = .popBack m t) (hpc : pc.val + 1 < maxPc) (l : List Sym) :
    ∀ (c : Cfg input), c.state = some ⟨k, pc, p2⟩ →
      Holds (c.workTapes t) (c.workTapePos t + 1 - l.length) l → (∀ s ∈ l, s ≠ m) →
      (c.workTapes t (c.workTapePos t - l.length) = some m ∨
        c.workTapes t (c.workTapePos t - l.length) = none) →
    ∃ c', Reach c (l.length + 1) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [t] ∧
      (∀ q, (q < c.workTapePos t + 1 - l.length ∨ c.workTapePos t < q) →
        c'.workTapes t q = c.workTapes t q) ∧
      BlankFrom (c'.workTapes t) (c.workTapePos t + 1 - l.length) l.length ∧
      c'.workTapePos t = c.workTapePos t - l.length + 1 := by sorry
