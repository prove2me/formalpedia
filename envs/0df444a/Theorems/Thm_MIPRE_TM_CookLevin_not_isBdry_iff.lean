-- Prove2me | Theorems.Thm_MIPRE_TM_CookLevin_not_isBdry_iff
-- name    : MIPRE.TM.CookLevin.not_isBdry_iff
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:19:29.363975+00:00
-- url     : https://prove2.me/theorems/ea8deb0f-5e36-4ca1-a7fb-e9eb41774189
-- title:
--   Lemma not_isBdry_iff of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.TM.CookLevin.Semantics` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The windows of a run are locally consistent. `localCfgOf M acc c js` is the local configuration read off a configuration `c` and its successor at the window `js`; its encoding is the assignment of the run on the window's variables (`encode_localCfgOf`), and it is locally consistent (`locallyConsistent_localCfgOf`): the completeness half of the tableau's correctness (`planning/succinct-cook-levin.md`, S1). The proof is the case analysis of the paper's `lem:correct-tableau` on where the heads are, with the clamping of the input heads (`Turing.moveInputPos`) matched against the tableau's rule…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.TM
--   open MIPRE.TM.CookLevin
--   open Turing MIPRE.SAT MultiInputTM
--   open MultiTapeTM (moveInputPos moveInputPos_zero)
--   variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
--
--   theorem MIPRE.TM.CookLevin.not_isBdry_iff (p : Pos S) : ¬ p.IsBdry ↔ 2 ≤ (p : ℕ) ∧ (p : ℕ) + 2 < numCells S
--   ```
--
--   **Formalization Note** `MIPRE.TM.CookLevin.not_isBdry_iff` is declared in `MIPRE/TM/CookLevin/Semantics.lean`, lines 43–44. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Semantics.lean#L43-L44

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

open MIPRE
open MIPRE.TM
open MIPRE.TM.CookLevin
open Turing MIPRE.SAT MultiInputTM
open MultiTapeTM (moveInputPos moveInputPos_zero)
variable {i w : ℕ} {Symbol State : Type*} [Fintype Symbol] [DecidableEq Symbol] [Fintype State]
  [DecidableEq State] {S : ℕ}

theorem MIPRE.TM.CookLevin.not_isBdry_iff (p : Pos S) : ¬ p.IsBdry ↔ 2 ≤ (p : ℕ) ∧ (p : ℕ) + 2 < numCells S := by sorry
