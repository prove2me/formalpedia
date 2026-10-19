-- Prove2me | Theorems.Thm_MIPRE_TM_CookLevin_Desc_length_encodeVar
-- name    : MIPRE.TM.CookLevin.Desc.length_encodeVar
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:18:38.606002+00:00
-- url     : https://prove2.me/theorems/55cfc267-5cb0-45cc-b0de-f08e01f15150
-- title:
--   Lemma length_encodeVar of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.TM.CookLevin.Layout` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The variable format of the describer. The binary format of the variables of the Cook–Levin tableau of the interpreter machine `U` (`planning/succinct-cook-levin.md`, S3). An index is a list of `m` bits, least significant first. With its top bit set it is *structured*: a tag (3 bits), the time `t` (`W` bits), the tape `d` (4), the position `p` (`W`), the cell value `v` (3), the state `q` (`Qb`), the thirteen window centers (`13 W`) and the gate `g` (`Gb`); tags `0..6` are `cell`, `head`, `state`, `emitOne`, `emitBad`, `emitted`, `aux`. With its top bit clear and value `j < 4T` it is an…
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
--   theorem MIPRE.TM.CookLevin.Desc.length_encodeVar (v : TabVar 7 6 Sym Ctl (Sof e) G) : (encodeVar e G v).length = mOf e G
--   ```
--
--   **Formalization Note** `MIPRE.TM.CookLevin.Desc.length_encodeVar` is declared in `MIPRE/TM/CookLevin/Layout.lean`, lines 438–439. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/TM/CookLevin/Layout.lean#L438-L439

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

open MIPRE
open MIPRE.TM
open MIPRE.TM.CookLevin
open MIPRE.TM.CookLevin.Desc
open MIPRE.TM.Interp MIPRE.SAT MIPRE.Cost
variable (e G : ℕ)

theorem MIPRE.TM.CookLevin.Desc.length_encodeVar (v : TabVar 7 6 Sym Ctl (Sof e) G) : (encodeVar e G v).length = mOf e G := by sorry
