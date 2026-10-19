-- Prove2me | Theorems.Thm_MIPRE_TM_CookLevin_Desc_evalFields_litFields
-- name    : MIPRE.TM.CookLevin.Desc.evalFields_litFields
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:18:22.646991+00:00
-- url     : https://prove2.me/theorems/c17ca248-9ac6-4214-ab91-6392caf82484
-- title:
--   The field formulas compute the fields of the index
-- statement:
--   A statement of the module `MIPRE.TM.CookLevin.FieldFml` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The fields of a literal, as formulas. For a literal whose `m` index bits are the input bits `b .. b + m`, the formulas computing its fields (`litFields`): the flag, the structured fields as slices of the input, and the answer decoding (`j < 2T`, `r = j` or `j - 2T`, `p = r / 2 + 3`, `v` from the parity of `r`), multiplexed by the flag. `evalFields_litFields` says that they compute exactly `fieldsOf` on the index (`planning/succinct-cook-levin.md`, S3).
--
--   **The field formulas compute the fields of the index.**
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.TM
--   open MIPRE.TM.CookLevin
--   open MIPRE.TM.CookLevin.Desc
--   open MIPRE.SAT MIPRE.Cost Fml
--   variable (e G T b : ℕ)
--   variable (x : ℕ → Bool)
--
--   theorem MIPRE.TM.CookLevin.Desc.evalFields_litFields (hT : T ≤ Sof e) :
--       evalFields (litFields e G T b) x = fieldsOf e G T (ibOf b (mOf e G) x)
--   ```
--
--   **Formalization Note** `MIPRE.TM.CookLevin.Desc.evalFields_litFields` is declared in `MIPRE/TM/CookLevin/FieldFml.lean`, lines 232–320. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/FieldFml.lean#L232-L320

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

open MIPRE
open MIPRE.TM
open MIPRE.TM.CookLevin
open MIPRE.TM.CookLevin.Desc
open MIPRE.SAT MIPRE.Cost Fml
variable (e G T b : ℕ)
variable (x : ℕ → Bool)

theorem MIPRE.TM.CookLevin.Desc.evalFields_litFields (hT : T ≤ Sof e) :
    evalFields (litFields e G T b) x = fieldsOf e G T (ibOf b (mOf e G) x) := by sorry
