-- Prove2me | Theorems.Thm_MIPRE_TM_CookLevin_cellCenter_cases
-- name    : MIPRE.TM.CookLevin.cellCenter_cases
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:15:12.782554+00:00
-- url     : https://prove2.me/theorems/7218f176-ab6b-4287-99f0-9a29047bee22
-- title:
--   At the window of a cell, either every head is in its window or the head of the cell's tape is far
-- statement:
--   A statement of the module `MIPRE.TM.CookLevin.Sound` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Soundness of the Cook–Levin tableau. A satisfying assignment of the tableau formula comes from an accepting run (`acceptsIn_of_tableau_sat`), and the equivalence `tableau_sat_iff` (`planning/succinct-cook-levin.md`, S1). * The successor part of a locally consistent window is a function of its time-`t` part (`post_of_pre`): two locally consistent local configurations with the same cells, heads and state at time `t`, one of them with at most one head per tape, agree on the cell and head at time `t + 1` of every tape whose head is far, and on everything when every head is in the window. * The…
--
--   At the window of a cell, either every head is in its window or the head of the cell's
--   tape is far.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.TM
--   open MIPRE.TM.CookLevin
--   open Turing MIPRE.SAT MultiInputTM
--   variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
--
--   theorem MIPRE.TM.CookLevin.cellCenter_cases (c : Cfg i w Symbol State input) (hin : HeadsIn c S) (d : Tape i w)
--       (p : Pos S) (hnb : ¬ p.IsBdry) :
--       (∀ d', ∃ δ : Fin 5, 1 ≤ (δ : ℕ) ∧ (δ : ℕ) ≤ 3 ∧
--         (localCfgOf M acc c (cellCenter c hin d p hnb)).HeadAt d' δ) ∨
--       (localCfgOf M acc c (cellCenter c hin d p hnb)).HeadFar d
--   ```
--
--   **Formalization Note** `MIPRE.TM.CookLevin.cellCenter_cases` is declared in `MIPRE/TM/CookLevin/Sound.lean`, lines 377–402. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Sound.lean#L377-L402

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
import Definitions.Def_MIPRE_TM_CookLevin_Sound

open MIPRE
open MIPRE.TM
open MIPRE.TM.CookLevin
open Turing MIPRE.SAT MultiInputTM
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S G : ℕ}
  (M : MultiInputTM i w Symbol State) (acc : Symbol) {input : Fin i → List Symbol}
omit [Fintype Symbol] [Fintype State] [DecidableEq State]

theorem MIPRE.TM.CookLevin.cellCenter_cases (c : Cfg i w Symbol State input) (hin : HeadsIn c S) (d : Tape i w)
    (p : Pos S) (hnb : ¬ p.IsBdry) :
    (∀ d', ∃ δ : Fin 5, 1 ≤ (δ : ℕ) ∧ (δ : ℕ) ≤ 3 ∧
      (localCfgOf M acc c (cellCenter c hin d p hnb)).HeadAt d' δ) ∨
    (localCfgOf M acc c (cellCenter c hin d p hnb)).HeadFar d := by sorry
