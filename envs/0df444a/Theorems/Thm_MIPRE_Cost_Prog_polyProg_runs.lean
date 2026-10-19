-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_polyProg_runs
-- name    : MIPRE.Cost.Prog.polyProg_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:57:04.998931+00:00
-- url     : https://prove2.me/theorems/0c17c864-ab32-4113-96ed-6e81699ff138
-- title:
--   polyProg cs evaluates the polynomial, within a cost polynomial in the argument
-- statement:
--   A statement of the module `MIPRE.Foundations.Halting.Arith` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Arithmetic in the ambient model: increment, unary conversion, multiplication, polynomials. The arithmetic the wrapper decider (`Halting/Wrapper.lean`) and the compressor's decider (`Halting/Compressor.lean`) need, each with its cost: * `Prog.incProg`: the successor of a canonical binary numeral (`Data.inc`, with `Data.inc_bits : inc n.bits = (n + 1).bits`), used to enumerate the bit queries; * `Prog.toUnaryProg`: a binary numeral to unary (`encode n ↦ ofNat n`), by the fold `k ↦ 2k + b` over the bits from the most significant one, doubling the unary accumulator with `revOntoProg`; *…
--
--   `polyProg cs` evaluates the polynomial, within a cost polynomial in the argument.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Cost
--   open MIPRE.Cost.Prog
--   open Polynomial
--   open MIPRE.Cost.Data
--
--   theorem MIPRE.Cost.Prog.polyProg_runs (cs : List ℕ) :
--       ∃ Q : Polynomial ℕ, ∀ (m : ℕ) (env : Env),
--         ∃ t ≤ Q.eval m, Eval (ofNat m :: env) (polyProg cs) (ofNat (polyEval cs m)) t
--   ```
--
--   **Formalization Note** `MIPRE.Cost.Prog.polyProg_runs` is declared in `MIPRE/Foundations/Halting/Arith.lean`, lines 612–657. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Arith.lean#L612-L657

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
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
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Halting_Arith_B

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open Polynomial
open MIPRE.Cost.Data

theorem MIPRE.Cost.Prog.polyProg_runs (cs : List ℕ) :
    ∃ Q : Polynomial ℕ, ∀ (m : ℕ) (env : Env),
      ∃ t ≤ Q.eval m, Eval (ofNat m :: env) (polyProg cs) (ofNat (polyEval cs m)) t := by sorry
