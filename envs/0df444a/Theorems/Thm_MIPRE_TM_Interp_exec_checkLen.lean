-- Prove2me | Theorems.Thm_MIPRE_TM_Interp_exec_checkLen
-- name    : MIPRE.TM.Interp.exec_checkLen
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:23:01.575+00:00
-- url     : https://prove2.me/theorems/0c75457b-690b-4a44-9dc9-4fbbd5a055af
-- title:
--   From position q + 1 on both j and ref, with |j| - q ≤ |ref| - q: both heads advance to the end of j
-- statement:
--   A statement of the module `MIPRE.TM.Interp.InputRoutines` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The input-tape routines. `copyUnary`, `copyInputBits`, `checkLen` and `buildAnswer` read an input tape from its head to the blank after the input, writing on a work tape; their specifications are by induction on the remaining suffix of the input.
--
--   From position `q + 1` on both `j` and `ref`, with `|j| - q ≤ |ref| - q`: both heads advance
--   to the end of `j`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.TM
--   open MIPRE.TM.Interp
--   open Turing MultiInputTM Phase MIPRE.Cost
--   open MultiTapeTM (moveInputPos)
--   variable {input : Fin 7 → List Sym}
--
--   theorem MIPRE.TM.Interp.exec_checkLen {k : ProgId} {pc : Fin maxPc} {j ref : IT}
--       (hins : instrAt k pc = .checkLen j ref) (hpc : pc.val + 1 < maxPc) (hjr : j ≠ ref) (m : ℕ) :
--       ∀ (c : Cfg input) (q : ℕ), c.state = at_ k pc → (c.inputPos j : ℕ) = q + 1 →
--         (c.inputPos ref : ℕ) = q + 1 → (input j).length = q + m → q + m ≤ (input ref).length →
--       ∃ c', Reach c (m + 1) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [j, ref] [] ∧
--         (c'.inputPos j : ℕ) = (input j).length + 1 ∧ (c'.inputPos ref : ℕ) = (input j).length + 1
--   ```
--
--   **Formalization Note** `MIPRE.TM.Interp.exec_checkLen` is declared in `MIPRE/TM/Interp/InputRoutines.lean`, lines 157–193. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/InputRoutines.lean#L157-L193

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
import Definitions.Def_MIPRE_TM_Interp_InputRoutines

open MIPRE
open MIPRE.TM
open MIPRE.TM.Interp
open Turing MultiInputTM Phase MIPRE.Cost
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}

theorem MIPRE.TM.Interp.exec_checkLen {k : ProgId} {pc : Fin maxPc} {j ref : IT}
    (hins : instrAt k pc = .checkLen j ref) (hpc : pc.val + 1 < maxPc) (hjr : j ≠ ref) (m : ℕ) :
    ∀ (c : Cfg input) (q : ℕ), c.state = at_ k pc → (c.inputPos j : ℕ) = q + 1 →
      (c.inputPos ref : ℕ) = q + 1 → (input j).length = q + m → q + m ≤ (input ref).length →
    ∃ c', Reach c (m + 1) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [j, ref] [] ∧
      (c'.inputPos j : ℕ) = (input j).length + 1 ∧ (c'.inputPos ref : ℕ) = (input j).length + 1 := by sorry
