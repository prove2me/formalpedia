-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_parseProg_wellScoped
-- name    : MIPRE.Cost.Prog.parseProg_wellScoped
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:22:09.527547+00:00
-- url     : https://prove2.me/theorems/8627b2a5-7790-4020-940e-aede70e6fbdb
-- title:
--   Lemma parseProg_wellScoped of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.Halting.Serial` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Reading and writing descriptions, in the ambient model. The two programs that move between a datum and its postorder serialization (`Data.toBitsPost`, `Halting/Descriptions.lean`): * `Prog.parseProg`: the stack machine `Data.stackRun` on a bit string, returning the top of the final stack (`Data.parse`). The compressor's decider reads the description it was handed with it (`Halting/Compressor.lean`). * `Prog.serProg`: the postorder serialization of a datum, by a loop over a list of pending items — a datum still to be written, or a marker for the closing `1` of a pair — accumulating the bits in…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Cost
--   open MIPRE.Cost.Prog
--   open MIPRE.Cost.Data
--
--   theorem MIPRE.Cost.Prog.parseProg_wellScoped : parseProg.WellScoped 1
--   ```
--
--   **Formalization Note** `MIPRE.Cost.Prog.parseProg_wellScoped` is declared in `MIPRE/Foundations/Halting/Serial.lean`, lines 102–102. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Serial.lean#L102-L102

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Halting_Serial

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open MIPRE.Cost.Data

theorem MIPRE.Cost.Prog.parseProg_wellScoped : parseProg.WellScoped 1 := by sorry
