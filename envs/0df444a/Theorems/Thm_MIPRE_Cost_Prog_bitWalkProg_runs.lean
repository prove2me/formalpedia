-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_bitWalkProg_runs
-- name    : MIPRE.Cost.Prog.bitWalkProg_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:22:45.75555+00:00
-- url     : https://prove2.me/theorems/9303ed20-c781-477b-aeb2-0c5435220034
-- title:
--   The bounded bit walk computes bitWalk l u, in time (|u| + 1) · (S + 21) for S dominating the sizes of l and u: linear in the input, times the budget
-- statement:
--   A statement of the module `MIPRE.Foundations.Halting.Lists` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Bounded walks over lists, in the ambient model. The programs with which the wrapper decider of `Halting/Wrapper.lean` performs the paper's format checks: the questions must be bit strings of the sampler's length, the answers bit strings within the answer-length budget, and equal questions must carry equal answers. All of them walk their input under a *budget*, so that their cost is the budget times the size of the input — the shape `T · (|input| + 1)` of `Decider.TimeBoundAt` — rather than a power of it. * `Prog.bitWalkProg`: on `cons l u`, walk `l` against the budget `u` (a list, typically a…
--
--   The bounded bit walk computes `bitWalk l u`, in time `(|u| + 1) · (S + 21)` for `S`
--   dominating the sizes of `l` and `u`: linear in the input, times the budget.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Cost
--   open MIPRE.Cost.Prog
--   open MIPRE.Cost.Data
--
--   theorem MIPRE.Cost.Prog.bitWalkProg_runs (l u : Data) (env : Env) (S : ℕ) (hS : l.size + u.size ≤ S) :
--       ∃ t ≤ (u.spine + 1) * (S + 21),
--         Eval (Data.cons l u :: env) bitWalkProg (bitWalk l u) t
--   ```
--
--   **Formalization Note** `MIPRE.Cost.Prog.bitWalkProg_runs` is declared in `MIPRE/Foundations/Halting/Lists.lean`, lines 310–349. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Halting/Lists.lean#L310-L349

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open MIPRE.Cost.Data

theorem MIPRE.Cost.Prog.bitWalkProg_runs (l u : Data) (env : Env) (S : ℕ) (hS : l.size + u.size ≤ S) :
    ∃ t ≤ (u.spine + 1) * (S + 21),
      Eval (Data.cons l u :: env) bitWalkProg (bitWalk l u) t := by sorry
