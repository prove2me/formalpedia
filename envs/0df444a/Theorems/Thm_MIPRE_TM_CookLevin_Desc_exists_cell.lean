-- Prove2me | Theorems.Thm_MIPRE_TM_CookLevin_Desc_exists_cell
-- name    : MIPRE.TM.CookLevin.Desc.exists_cell
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:18:04.896716+00:00
-- url     : https://prove2.me/theorems/d0c9923d-5e87-48cc-b52b-50509855ba58
-- title:
--   Lemma exists_cell of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.TM.CookLevin.Families` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The clause families of the tableau, on decoded fields. A *candidate* clause is three field records and three signs (`Cand`): what the describer reads off its `3m + 3` input bits. `Cand.Dec c cl` says the candidate decodes to the tableau clause `cl` (each record to the variable of the corresponding literal, each sign to its polarity). For each sub-family of the tableau of the interpreter machine (`startClauses`, `freeClauses`, `bdryClauses`, `emitClauses`, `finalClauses` of `Tableau.lean`) this file gives a predicate on candidates, stated on the numeric fields alone, and proves it exact: it…
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
--
--   theorem MIPRE.TM.CookLevin.Desc.exists_cell {F : Fields} (h : IsCell e F) :
--       ∃ (t : Fin (Sof e + 1)) (d : Tape 7 6) (p : Pos (Sof e)) (v : CellVal Sym),
--         decodeVar e G F = some (.cell t d p v)
--   ```
--
--   **Formalization Note** `MIPRE.TM.CookLevin.Desc.exists_cell` is declared in `MIPRE/TM/CookLevin/Families.lean`, lines 127–140. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Families.lean#L127-L140

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

open MIPRE
open MIPRE.TM
open MIPRE.TM.CookLevin
open MIPRE.TM.CookLevin.Desc
open MIPRE.TM.Interp MIPRE.SAT MIPRE.Cost
variable (e G : ℕ)

theorem MIPRE.TM.CookLevin.Desc.exists_cell {F : Fields} (h : IsCell e F) :
    ∃ (t : Fin (Sof e + 1)) (d : Tape 7 6) (p : Pos (Sof e)) (v : CellVal Sym),
      decodeVar e G F = some (.cell t d p v) := by sorry
