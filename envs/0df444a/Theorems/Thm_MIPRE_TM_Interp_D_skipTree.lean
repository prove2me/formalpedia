-- Prove2me | Theorems.Thm_MIPRE_TM_Interp_D_skipTree
-- name    : MIPRE.TM.Interp.D_skipTree
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:21:43.030751+00:00
-- url     : https://prove2.me/theorems/651fb279-5261-4b31-8e1e-fbd8914286b4
-- title:
--   Lemma D_skipTree of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.TM.Interp.Desc` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Tape descriptions. A work tape is described by the list it holds from cell `0` (blank elsewhere) and its head position; a configuration by its control and the six descriptions (`Desc`). Every routine becomes a transformation of descriptions (`D_write`, `D_copyTree`, …), so that the correctness of a step of the evaluation machine is a chain of such transformations followed by list algebra (`overwrite`).
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.TM
--   open MIPRE.TM.Interp
--   open Turing MultiInputTM Phase MIPRE.Cost
--   variable {input : Fin 7 → List Sym}
--   variable {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {ds : WT → TapeSt}
--
--   theorem MIPRE.TM.Interp.D_skipTree {src : WT} (hins : instrAt k pc = .copyTree src none false)
--       (hpc : pc.val + 1 < maxPc) (hsc : src ≠ CNT) (hd : Desc c (at_ k pc) ds)
--       (hcnt : ds CNT = ⟨[], 0⟩) {v : Data} {l₁ l₂ : List Sym}
--       (hsrc : (ds src).l = l₁ ++ S v ++ l₂) (hsp : (ds src).p = l₁.length) :
--       ∃ n ≤ 3 * v.size + 1, ∃ c', Reach c n c' [] ∧
--         Desc c' (next_ k pc hpc) (Function.update ds src ⟨(ds src).l, l₁.length + v.size⟩)
--   ```
--
--   **Formalization Note** `MIPRE.TM.Interp.D_skipTree` is declared in `MIPRE/TM/Interp/Desc.lean`, lines 596–619. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/Interp/Desc.lean#L596-L619

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
import Definitions.Def_MIPRE_TM_Interp_Desc

open MIPRE
open MIPRE.TM
open MIPRE.TM.Interp
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
variable {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {ds : WT → TapeSt}

theorem MIPRE.TM.Interp.D_skipTree {src : WT} (hins : instrAt k pc = .copyTree src none false)
    (hpc : pc.val + 1 < maxPc) (hsc : src ≠ CNT) (hd : Desc c (at_ k pc) ds)
    (hcnt : ds CNT = ⟨[], 0⟩) {v : Data} {l₁ l₂ : List Sym}
    (hsrc : (ds src).l = l₁ ++ S v ++ l₂) (hsp : (ds src).p = l₁.length) :
    ∃ n ≤ 3 * v.size + 1, ∃ c', Reach c n c' [] ∧
      Desc c' (next_ k pc hpc) (Function.update ds src ⟨(ds src).l, l₁.length + v.size⟩) := by sorry
