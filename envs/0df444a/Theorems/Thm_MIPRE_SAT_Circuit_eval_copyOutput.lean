-- Prove2me | Theorems.Thm_MIPRE_SAT_Circuit_eval_copyOutput
-- name    : MIPRE.SAT.Circuit.eval_copyOutput
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:12:42.530039+00:00
-- url     : https://prove2.me/theorems/5bec2399-f532-4ca3-b013-a3b40d73776a
-- title:
--   A copying gate preserves the circuit's value
-- statement:
--   A statement of the module `MIPRE.Foundations.SAT.GatePadding` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Exact gate-count padding. Our circuit representation designates its last gate as the output. To add any number of gates while retaining that convention, append copying OR gates, each reading the previous output twice. Every former output has fan-out two; the new output is terminal. This realizes the exact-size padding required by `prop:explicit-padded-succinct-deciders`, without a separate output-wire index.
--
--   A copying gate preserves the circuit's value.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SAT
--   open MIPRE.SAT.Circuit
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun
--
--   theorem MIPRE.SAT.Circuit.eval_copyOutput (C : Circuit) (hne : C.gates ≠ []) (x : ℕ → Bool) :
--       (copyOutput C).eval x = C.eval x
--   ```
--
--   **Formalization Note** `MIPRE.SAT.Circuit.eval_copyOutput` is declared in `MIPRE/Foundations/SAT/GatePadding.lean`, lines 40–53. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/GatePadding.lean#L40-L53

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
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
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_Foundations_SAT_GatePadding

open MIPRE
open MIPRE.SAT
open MIPRE.SAT.Circuit
open MIPRE.Cost MIPRE.Cost.PolyTimeFun

theorem MIPRE.SAT.Circuit.eval_copyOutput (C : Circuit) (hne : C.gates ≠ []) (x : ℕ → Bool) :
    (copyOutput C).eval x = C.eval x := by sorry
