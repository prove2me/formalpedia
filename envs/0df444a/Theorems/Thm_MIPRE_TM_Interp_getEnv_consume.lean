-- Prove2me | Theorems.Thm_MIPRE_TM_Interp_getEnv_consume
-- name    : MIPRE.TM.Interp.getEnv_consume
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:21:49.980978+00:00
-- url     : https://prove2.me/theorems/f22048c3-5b03-4eb2-b3c2-9184002284ed
-- title:
--   Phases p6/p7: consume the index S(ofNat j) on C, then write nil on X and move E one right, at p9
-- statement:
--   A statement of the module `MIPRE.TM.Interp.GetEnv` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The `getEnv` routine. With the unary index `S(ofNat i)` under the head of `C` and the environment `envRepr env` on `E` with its head at the end, `getEnv` writes `S(env.get i)` at the head of `X`: it walks left over `i` separators (phases `p1`–`p3`), then to the start of the element (`p4`), copies it (`p5`) and returns the head of `E` to the end (`p8`); past the start of the environment the index is out of range, the rest of it is consumed (`p6`, `p7`) and `nil` is written (`p9`). The proof is by induction on the index, over the suffix of the environment not yet passed.
--
--   Phases `p6`/`p7`: consume the index `S(ofNat j)` on `C`, then write `nil` on `X` and move
--   `E` one right, at `p9`.
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
--   theorem MIPRE.TM.Interp.getEnv_consume {k : ProgId} {pc : Fin maxPc} (hins : instrAt k pc = .getEnv) (j : ℕ) :
--       ∀ (c : Cfg input), c.state = some ⟨k, pc, p6⟩ →
--         Holds (c.workTapes C) (c.workTapePos C) (S (Data.ofNat j)) →
--       ∃ c', Reach c (2 * j + 1) c' [] ∧ c'.state = some ⟨k, pc, p9⟩ ∧ Untouched c c' [] [C, E, X] ∧
--         c'.workTapes C = c.workTapes C ∧ c'.workTapePos C = c.workTapePos C + (2 * j + 1 : ℕ) ∧
--         c'.workTapes E = c.workTapes E ∧ c'.workTapePos E = c.workTapePos E + 1 ∧
--         DstEff X c c' [.zero]
--   ```
--
--   **Formalization Note** `MIPRE.TM.Interp.getEnv_consume` is declared in `MIPRE/TM/Interp/GetEnv.lean`, lines 276–348. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/GetEnv.lean#L276-L348

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
import Definitions.Def_MIPRE_TM_Interp_GetEnv

open MIPRE
open MIPRE.TM
open MIPRE.TM.Interp
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}

theorem MIPRE.TM.Interp.getEnv_consume {k : ProgId} {pc : Fin maxPc} (hins : instrAt k pc = .getEnv) (j : ℕ) :
    ∀ (c : Cfg input), c.state = some ⟨k, pc, p6⟩ →
      Holds (c.workTapes C) (c.workTapePos C) (S (Data.ofNat j)) →
    ∃ c', Reach c (2 * j + 1) c' [] ∧ c'.state = some ⟨k, pc, p9⟩ ∧ Untouched c c' [] [C, E, X] ∧
      c'.workTapes C = c.workTapes C ∧ c'.workTapePos C = c.workTapePos C + (2 * j + 1 : ℕ) ∧
      c'.workTapes E = c.workTapes E ∧ c'.workTapePos E = c.workTapePos E + 1 ∧
      DstEff X c c' [.zero] := by sorry
