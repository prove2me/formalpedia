-- Prove2me | Theorems.Thm_MIPRE_TM_CookLevin_Desc_eval_isAuxF
-- name    : MIPRE.TM.CookLevin.Desc.eval_isAuxF
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:18:37.476988+00:00
-- url     : https://prove2.me/theorems/866c4255-8142-4637-abba-0d5dd57f75a8
-- title:
--   Lemma eval_isAuxF of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.TM.CookLevin.Kinds` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The kinds of variables, on fields and as formulas. For the fields `F` of an index, the predicates `IsCell`, `IsHead`, … saying that `F` denotes a variable of that kind (with its range checks), the characterization of `decodeVar` by them (`decodeVar_cell_iff`, …), the numeric equality of two fields records (`Fields.numEq`, the same variable up to the aliasing of unused fields), and the formulas computing all of these on the field formulas of a literal (`isCellF`, `numEqF`, …) with their semantics (`planning/succinct-cook-levin.md`, S3).
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.TM
--   open MIPRE.TM.CookLevin
--   open MIPRE.TM.CookLevin.Desc
--   open MIPRE.SAT MIPRE.Cost Fml
--   variable (e G : ℕ)
--   variable {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool)
--
--   theorem MIPRE.TM.CookLevin.Desc.eval_isAuxF : (isAuxF e G A).eval x = true ↔ IsAux e G (evalFields A x)
--   ```
--
--   **Formalization Note** `MIPRE.TM.CookLevin.Desc.eval_isAuxF` is declared in `MIPRE/TM/CookLevin/Kinds.lean`, lines 482–505. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Kinds.lean#L482-L505

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

open MIPRE
open MIPRE.TM
open MIPRE.TM.CookLevin
open MIPRE.TM.CookLevin.Desc
open MIPRE.SAT MIPRE.Cost Fml
variable (e G : ℕ)
variable {A : FieldsF} (hA : A.Lengths e G) (x : ℕ → Bool)
include hA

theorem MIPRE.TM.CookLevin.Desc.eval_isAuxF : (isAuxF e G A).eval x = true ↔ IsAux e G (evalFields A x) := by sorry
