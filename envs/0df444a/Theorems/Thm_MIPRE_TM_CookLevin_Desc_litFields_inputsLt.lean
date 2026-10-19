-- Prove2me | Theorems.Thm_MIPRE_TM_CookLevin_Desc_litFields_inputsLt
-- name    : MIPRE.TM.CookLevin.Desc.litFields_inputsLt
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:18:18.167991+00:00
-- url     : https://prove2.me/theorems/3c194f57-402d-4ad9-8b92-0c79f937f41a
-- title:
--   Lemma litFields_inputsLt of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.TM.CookLevin.FamilyFml` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The clause families as formulas. For each family predicate of `Families.lean` and `Window.lean`, the formula computing it on a candidate of field formulas (`CandF`: three `FieldsF` and three sign formulas), with its exact semantics (`eval_startF`, …, `eval_windowF`) and its input bound. The fixed input tapes enter through value formulas (`cellValF` for a listed string, `unaryValF` for the unary time bound), tied to `fixed` by `TapeSpec`; the free tapes through the list of their indices (`FreeSpec`) (`planning/succinct-cook-levin.md`, S3).
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.TM
--   open MIPRE.TM.CookLevin
--   open MIPRE.TM.CookLevin.Desc
--   open MIPRE.TM.Interp MIPRE.SAT MIPRE.Cost Fml
--   variable (e G T b n : ℕ) (hn : b + mOf e G ≤ n)
--
--   theorem MIPRE.TM.CookLevin.Desc.litFields_inputsLt : (litFields e G T b).InputsLt n
--   ```
--
--   **Formalization Note** `MIPRE.TM.CookLevin.Desc.litFields_inputsLt` is declared in `MIPRE/TM/CookLevin/FamilyFml.lean`, lines 221–239. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/FamilyFml.lean#L221-L239

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
import Definitions.Def_MIPRE_TM_CookLevin_FamilyFml

open MIPRE
open MIPRE.TM
open MIPRE.TM.CookLevin
open MIPRE.TM.CookLevin.Desc
open MIPRE.TM.Interp MIPRE.SAT MIPRE.Cost Fml
variable (e G T b n : ℕ) (hn : b + mOf e G ≤ n)
include hn

theorem MIPRE.TM.CookLevin.Desc.litFields_inputsLt : (litFields e G T b).InputsLt n := by sorry
