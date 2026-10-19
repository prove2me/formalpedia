-- Prove2me | Theorems.Thm_MIPRE_TM_CookLevin_chk_eval_run
-- name    : MIPRE.TM.CookLevin.chk_eval_run
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:17:49.983985+00:00
-- url     : https://prove2.me/theorems/6c241867-247c-4247-bac0-2c9931c7ee70
-- title:
--   The check circuit accepts every window of the run
-- statement:
--   A statement of the module `MIPRE.TM.CookLevin.Correct` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Correctness of the Cook–Levin tableau. The tableau formula of `S` steps of a machine `M` (`tableau`) is satisfiable, with the fixed input tapes holding their strings, iff `M` accepts some completion of the free input tapes within `S` steps (`planning/succinct-cook-levin.md`, S1; `answer_reduction.tex` `lem:correct-tableau`). Acceptance is `AcceptsIn`: halted at time `S` with output string exactly `[acc]`. * **Completeness** (`tableau_sat_of_acceptsIn`): the assignment of an accepting run (`runAssign`) satisfies every clause; the window clauses because the windows of a run are locally…
--
--   The check circuit accepts every window of the run.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.TM
--   open MIPRE.TM.CookLevin
--   open Turing MIPRE.SAT MultiInputTM
--   open MultiTapeTM (moveInputPos)
--   variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
--   variable (chk : Circuit)
--   variable {G : ℕ}
--
--   theorem MIPRE.TM.CookLevin.chk_eval_run (hchk : IsCheckCircuit M acc chk) (t : Fin S) (js : Tape i w → Center S) :
--       chk.eval (fun n => baseAssign M acc (input := input) chk.gates.length
--         (inpOf (G := chk.gates.length) t js n)) = true
--   ```
--
--   **Formalization Note** `MIPRE.TM.CookLevin.chk_eval_run` is declared in `MIPRE/TM/CookLevin/Correct.lean`, lines 307–323. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Correct.lean#L307-L323

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Computability.Language
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Relation
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_CookLevin_Semantics
import Definitions.Def_MIPRE_TM_CookLevin_Correct

open MIPRE
open MIPRE.TM
open MIPRE.TM.CookLevin
open Turing MIPRE.SAT MultiInputTM
open MultiTapeTM (moveInputPos)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
variable (chk : Circuit)
variable {G : ℕ}

theorem MIPRE.TM.CookLevin.chk_eval_run (hchk : IsCheckCircuit M acc chk) (t : Fin S) (js : Tape i w → Center S) :
    chk.eval (fun n => baseAssign M acc (input := input) chk.gates.length
      (inpOf (G := chk.gates.length) t js n)) = true := by sorry
