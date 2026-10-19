-- Prove2me | Theorems.Thm_MIPRE_TM_CookLevin_post_of_pre
-- name    : MIPRE.TM.CookLevin.post_of_pre
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:15:09.329364+00:00
-- url     : https://prove2.me/theorems/794dd86d-b118-4be9-820f-b75fcdf79dfd
-- title:
--   The successor part of a locally consistent window is determined by its time-t part. For every tape whose head is far the cell and head at time t + 1, and when every head…
-- statement:
--   A statement of the module `MIPRE.TM.CookLevin.Sound` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Soundness of the Cook–Levin tableau. A satisfying assignment of the tableau formula comes from an accepting run (`acceptsIn_of_tableau_sat`), and the equivalence `tableau_sat_iff` (`planning/succinct-cook-levin.md`, S1). * The successor part of a locally consistent window is a function of its time-`t` part (`post_of_pre`): two locally consistent local configurations with the same cells, heads and state at time `t`, one of them with at most one head per tape, agree on the cell and head at time `t + 1` of every tape whose head is far, and on everything when every head is in the window. * The…
--
--   **The successor part of a locally consistent window is determined by its time-`t`
--   part.** For every tape whose head is far the cell and head at time `t + 1`, and when every
--   head is in the window everything.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.TM
--   open MIPRE.TM.CookLevin
--   open Turing MIPRE.SAT MultiInputTM
--   variable {i w : ℕ} {Symbol State : Type*} [DecidableEq Symbol] [DecidableEq State]
--
--   theorem MIPRE.TM.CookLevin.post_of_pre {L L' : LocalCfg i w Symbol State} (hL : LocallyConsistent M acc L)
--       (hL' : LocallyConsistent M acc L') (hno : ∀ d, ¬ L'.TwoHeads d)
--       (hc : L.cellPre = L'.cellPre) (hh : L.headPre = L'.headPre) (hs : L.statePre = L'.statePre) :
--       (∀ d, L'.HeadFar d → L.cellPost d = L'.cellPost d ∧ L.headPost d = L'.headPost d) ∧
--       ((∀ d, ∃ δ : Fin 5, 1 ≤ (δ : ℕ) ∧ (δ : ℕ) ≤ 3 ∧ L'.HeadAt d δ) →
--         L.cellPost = L'.cellPost ∧ L.headPost = L'.headPost ∧ L.statePost = L'.statePost ∧
--           L.emitOne = L'.emitOne ∧ L.emitBad = L'.emitBad)
--   ```
--
--   **Formalization Note** `MIPRE.TM.CookLevin.post_of_pre` is declared in `MIPRE/TM/CookLevin/Sound.lean`, lines 86–120. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Sound.lean#L86-L120

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
variable {i w : ℕ} {Symbol State : Type*} [DecidableEq Symbol] [DecidableEq State]
  (M : MultiInputTM i w Symbol State) (acc : Symbol)
omit [DecidableEq State]

theorem MIPRE.TM.CookLevin.post_of_pre {L L' : LocalCfg i w Symbol State} (hL : LocallyConsistent M acc L)
    (hL' : LocallyConsistent M acc L') (hno : ∀ d, ¬ L'.TwoHeads d)
    (hc : L.cellPre = L'.cellPre) (hh : L.headPre = L'.headPre) (hs : L.statePre = L'.statePre) :
    (∀ d, L'.HeadFar d → L.cellPost d = L'.cellPost d ∧ L.headPost d = L'.headPost d) ∧
    ((∀ d, ∃ δ : Fin 5, 1 ≤ (δ : ℕ) ∧ (δ : ℕ) ≤ 3 ∧ L'.HeadAt d δ) →
      L.cellPost = L'.cellPost ∧ L.headPost = L'.headPost ∧ L.statePost = L'.statePost ∧
        L.emitOne = L'.emitOne ∧ L.emitBad = L'.emitBad) := by sorry
