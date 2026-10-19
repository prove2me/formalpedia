-- Prove2me | Theorems.Thm_MIPRE_TM_CookLevin_Desc_windowPred_iff
-- name    : MIPRE.TM.CookLevin.Desc.windowPred_iff
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:19:50.789914+00:00
-- url     : https://prove2.me/theorems/dadfaaaf-1b4b-4b53-9fda-de87efd88650
-- title:
--   The window family is exact: a candidate satisfies WindowPred iff it decodes to a window clause of the tableau
-- statement:
--   A statement of the module `MIPRE.TM.CookLevin.Window` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The window family, on decoded fields. The window clauses of the tableau are the Tseitin clauses of the check circuit `chk` at every step `t` and window `js` (`windowClauses`). Every such clause has a gate literal (`aux t js g`) in its third position: the *templates* of a gate (`gateTemplates`) list its clauses as triples of literal *specs* — a gate index (`.aux u`) or a window input (`.win n`) — with their signs, and the clause is recovered from the templates by instantiating the specs at `(t, js)` (`gateClauses_eq_templates`). A candidate matches a template when its third record is a gate…
--
--   **The window family is exact**: a candidate satisfies `WindowPred` iff it decodes to a
--   window clause of the tableau.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.TM
--   open MIPRE.TM.CookLevin
--   open MIPRE.TM.CookLevin.Desc
--   open MIPRE.TM.Interp MIPRE.SAT MIPRE.Cost
--   variable (e G : ℕ)
--   variable (chk : Circuit) (hC : chk.RefsLt) (hin : chk.InputsLt)
--
--   theorem MIPRE.TM.CookLevin.Desc.windowPred_iff (c : Cand) :
--       WindowPred e chk.gates.length chk c ↔
--         ∃ cl ∈ windowClauses (S := Sof e) chk, c.Dec e chk.gates.length cl
--   ```
--
--   **Formalization Note** `MIPRE.TM.CookLevin.Desc.windowPred_iff` is declared in `MIPRE/TM/CookLevin/Window.lean`, lines 205–253. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Window.lean#L205-L253

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Language
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_CookLevin_Local
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_TM_CookLevin_Tableau
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_CookLevin_Layout
import Definitions.Def_MIPRE_TM_CookLevin_FieldFml
import Definitions.Def_MIPRE_TM_CookLevin_Kinds
import Definitions.Def_MIPRE_TM_CookLevin_Families
import Definitions.Def_MIPRE_TM_CookLevin_Window

open MIPRE
open MIPRE.TM
open MIPRE.TM.CookLevin
open MIPRE.TM.CookLevin.Desc
open MIPRE.TM.Interp MIPRE.SAT MIPRE.Cost
variable (e G : ℕ)
variable (chk : Circuit) (hC : chk.RefsLt) (hin : chk.InputsLt)
  (hinp : chk.inputs = winCard 7 6 Sym Ctl) (hne : chk.gates ≠ [])
include hC hin hinp hne

theorem MIPRE.TM.CookLevin.Desc.windowPred_iff (c : Cand) :
    WindowPred e chk.gates.length chk c ↔
      ∃ cl ∈ windowClauses (S := Sof e) chk, c.Dec e chk.gates.length cl := by sorry
