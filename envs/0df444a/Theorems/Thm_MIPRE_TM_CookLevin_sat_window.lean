-- Prove2me | Theorems.Thm_MIPRE_TM_CookLevin_sat_window
-- name    : MIPRE.TM.CookLevin.sat_window
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:15:34.49009+00:00
-- url     : https://prove2.me/theorems/40411167-26c6-46c2-b9a7-cbbb659e3891
-- title:
--   The window clauses force, through the check circuit, local consistency of every window
-- statement:
--   A statement of the module `MIPRE.TM.CookLevin.Sound` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Soundness of the Cook–Levin tableau. A satisfying assignment of the tableau formula comes from an accepting run (`acceptsIn_of_tableau_sat`), and the equivalence `tableau_sat_iff` (`planning/succinct-cook-levin.md`, S1). * The successor part of a locally consistent window is a function of its time-`t` part (`post_of_pre`): two locally consistent local configurations with the same cells, heads and state at time `t`, one of them with at most one head per tape, agree on the cell and head at time `t + 1` of every tape whose head is far, and on everything when every head is in the window. * The…
--
--   The window clauses force, through the check circuit, local consistency of every
--   window.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.TM
--   open MIPRE.TM.CookLevin
--   open Turing MIPRE.SAT MultiInputTM
--   variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
--   variable (hSat : (tableau M s₀ s₁ S fixed chk).Sat a)
--
--   theorem MIPRE.TM.CookLevin.sat_window (hchk : IsCheckCircuit M acc chk) (hC : chk.RefsLt) (hin : chk.InputsLt)
--       (hne : chk.gates ≠ []) (t : Fin S) (js : Tape i w → Center S) :
--       checkPred M acc (fun v => a (winVarOf (G := chk.gates.length) t js v))
--   ```
--
--   **Formalization Note** `MIPRE.TM.CookLevin.sat_window` is declared in `MIPRE/TM/CookLevin/Sound.lean`, lines 588–603. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Sound.lean#L588-L603

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
  [DecidableEq State] {S : ℕ}
  (M : MultiInputTM i w Symbol State) (acc s₀ s₁ : Symbol) (fixed : Fin i → Option (List Symbol))
  (chk : Circuit) (a : TabVar i w Symbol State S chk.gates.length → Bool)
variable (hSat : (tableau M s₀ s₁ S fixed chk).Sat a)
include hSat

theorem MIPRE.TM.CookLevin.sat_window (hchk : IsCheckCircuit M acc chk) (hC : chk.RefsLt) (hin : chk.InputsLt)
    (hne : chk.gates ≠ []) (t : Fin S) (js : Tape i w → Center S) :
    checkPred M acc (fun v => a (winVarOf (G := chk.gates.length) t js v)) := by sorry
