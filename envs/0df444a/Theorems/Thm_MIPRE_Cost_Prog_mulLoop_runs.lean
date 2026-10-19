-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_mulLoop_runs
-- name    : MIPRE.Cost.Prog.mulLoop_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:55:24.553858+00:00
-- url     : https://prove2.me/theorems/0ea3644e-dea4-4e16-b05d-7fcfbeb13baa
-- title:
--   The multiplication loop: from (ofNat b, ofNat acc) with a one variable out, to ofNat (acc + a b)
-- statement:
--   A statement of the module `MIPRE.Foundations.Halting.Arith` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Arithmetic in the ambient model: increment, unary conversion, multiplication, polynomials. The arithmetic the wrapper decider (`Halting/Wrapper.lean`) and the compressor's decider (`Halting/Compressor.lean`) need, each with its cost: * `Prog.incProg`: the successor of a canonical binary numeral (`Data.inc`, with `Data.inc_bits : inc n.bits = (n + 1).bits`), used to enumerate the bit queries; * `Prog.toUnaryProg`: a binary numeral to unary (`encode n ↦ ofNat n`), by the fold `k ↦ 2k + b` over the bits from the most significant one, doubling the unary accumulator with `revOntoProg`; *…
--
--   The multiplication loop: from `(ofNat b, ofNat acc)` with `a` one variable out, to
--   `ofNat (acc + a b)`.
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
--   theorem MIPRE.Cost.Prog.mulLoop_runs (a b acc : ℕ) (rest : Env) (P : ℕ) (hP : acc + a * b ≤ P) :
--       ∃ t ≤ (b + 1) * ((a + 1) * (4 * a + 2 * P + 15) + 4 * a + 4 * P + 2 * b + 41),
--         Eval (Data.cons (ofNat b) (ofNat acc) :: ofNat a :: rest) (.loop mulBody)
--           (ofNat (acc + a * b)) t
--   ```
--
--   **Formalization Note** `MIPRE.Cost.Prog.mulLoop_runs` is declared in `MIPRE/Foundations/Halting/Arith.lean`, lines 547–577. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Arith.lean#L547-L577

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

theorem MIPRE.Cost.Prog.mulLoop_runs (a b acc : ℕ) (rest : Env) (P : ℕ) (hP : acc + a * b ≤ P) :
    ∃ t ≤ (b + 1) * ((a + 1) * (4 * a + 2 * P + 15) + 4 * a + 4 * P + 2 * b + 41),
      Eval (Data.cons (ofNat b) (ofNat acc) :: ofNat a :: rest) (.loop mulBody)
        (ofNat (acc + a * b)) t := by sorry
