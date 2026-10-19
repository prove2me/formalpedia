-- Prove2me | Theorems.Thm_MIPRE_TM_Interp_exec_popBack
-- name    : MIPRE.TM.Interp.exec_popBack
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:23:46.937209+00:00
-- url     : https://prove2.me/theorems/a3175cf1-e058-440e-ba09-1ea29d196fd6
-- title:
--   popBack: from the end pos, with l ++ [a] on pos - |l| - 1 … pos - 1, l free of m, and the marker or a blank before: erase them, ending at pos - |l| - 1
-- statement:
--   A statement of the module `MIPRE.TM.Interp.Routines` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The routines: specifications of the instructions. Each instruction's specification is a reachability statement: from a configuration at the instruction's first phase, with the tapes it reads in a stated shape, a bounded number of steps leads to the configuration at the next instruction, with the stated effect on the tapes it touches and none on the others (`Untouched`).
--
--   `popBack`: from the end `pos`, with `l ++ [a]` on `pos - |l| - 1 … pos - 1`, `l` free of
--   `m`, and the marker or a blank before: erase them, ending at `pos - |l| - 1`.
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
--   theorem MIPRE.TM.Interp.exec_popBack {k : ProgId} {pc : Fin maxPc} {m : Sym} {t : WT}
--       (hins : instrAt k pc = .popBack m t) (hpc : pc.val + 1 < maxPc) (l : List Sym) (a : Sym)
--       (c : Cfg input) (hq : c.state = at_ k pc)
--       (hl : Holds (c.workTapes t) (c.workTapePos t - l.length - 1) (l ++ [a])) (hm : ∀ s ∈ l, s ≠ m)
--       (hend : c.workTapes t (c.workTapePos t - l.length - 2) = some m ∨
--         c.workTapes t (c.workTapePos t - l.length - 2) = none) :
--       ∃ c', Reach c (l.length + 3) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [t] ∧
--         (∀ q, (q < c.workTapePos t - l.length - 1 ∨ c.workTapePos t ≤ q) →
--           c'.workTapes t q = c.workTapes t q) ∧
--         BlankFrom (c'.workTapes t) (c.workTapePos t - l.length - 1) (l.length + 1) ∧
--         c'.workTapePos t = c.workTapePos t - l.length - 1
--   ```
--
--   **Formalization Note** `MIPRE.TM.Interp.exec_popBack` is declared in `MIPRE/TM/Interp/Routines.lean`, lines 794–852. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/Routines.lean#L794-L852

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

theorem MIPRE.TM.Interp.exec_popBack {k : ProgId} {pc : Fin maxPc} {m : Sym} {t : WT}
    (hins : instrAt k pc = .popBack m t) (hpc : pc.val + 1 < maxPc) (l : List Sym) (a : Sym)
    (c : Cfg input) (hq : c.state = at_ k pc)
    (hl : Holds (c.workTapes t) (c.workTapePos t - l.length - 1) (l ++ [a])) (hm : ∀ s ∈ l, s ≠ m)
    (hend : c.workTapes t (c.workTapePos t - l.length - 2) = some m ∨
      c.workTapes t (c.workTapePos t - l.length - 2) = none) :
    ∃ c', Reach c (l.length + 3) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [t] ∧
      (∀ q, (q < c.workTapePos t - l.length - 1 ∨ c.workTapePos t ≤ q) →
        c'.workTapes t q = c.workTapes t q) ∧
      BlankFrom (c'.workTapes t) (c.workTapePos t - l.length - 1) (l.length + 1) ∧
      c'.workTapePos t = c.workTapePos t - l.length - 1 := by sorry
