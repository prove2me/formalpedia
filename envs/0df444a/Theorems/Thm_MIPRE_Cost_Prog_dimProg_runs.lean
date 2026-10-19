-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_dimProg_runs
-- name    : MIPRE.Cost.Prog.dimProg_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:26:46.820987+00:00
-- url     : https://prove2.me/theorems/7dfbf3ef-edc6-493d-80f0-0fa027d59b70
-- title:
--   Lemma dimProg_runs of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.Repeat.Sampler` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The program of the repeated sampler. The sampler of `ComputeParrepVerifier` (`thm:parallel-repetition`; `planning/repetition-verifier.md`, R3(b)) as a program of the ambient model. It is one fixed program `repSampCore univ` — `univ` a universal machine — run through the s-m-n construction `hardcode` on the datum `(S̄, λ, τ)`: its input is then `((S̄, λ, τ), (n, q))`, with `S̄` the input sampler's program, `λ, τ` in binary and `q` a query. It 1. asks `S̄` for its dimension `s = s(n)`, through `univ`; 2. on the dimension query (`kind = 0`, i.e. `nil`) runs `dimProg`: the numeral `2^m s` with `m…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Cost
--   open MIPRE.Cost.Prog
--   open MIPRE.Cost.Data
--
--   theorem MIPRE.Cost.Prog.dimProg_runs (tau : ℕ) (bl bn : List Data) (h : Data) (l : List Data) :
--       ∃ t ≤ dimCost tau (bl.length + bn.length) (list bl).size (list bn).size (list (h :: l)).size,
--         Eval [Data.cons (list (h :: l)) (.cons (list bl) (.cons (list bn) (encode tau)))] dimProg
--           (list (List.replicate (tau * (bl.length + bn.length)) .nil ++ (h :: l))) t
--   ```
--
--   **Formalization Note** `MIPRE.Cost.Prog.dimProg_runs` is declared in `MIPRE/Foundations/Repeat/Sampler.lean`, lines 68–94. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Repeat/Sampler.lean#L68-L94

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_Repeat_MapLoop
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Repeat_Sampler

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open MIPRE.Cost.Data

theorem MIPRE.Cost.Prog.dimProg_runs (tau : ℕ) (bl bn : List Data) (h : Data) (l : List Data) :
    ∃ t ≤ dimCost tau (bl.length + bn.length) (list bl).size (list bn).size (list (h :: l)).size,
      Eval [Data.cons (list (h :: l)) (.cons (list bl) (.cons (list bn) (encode tau)))] dimProg
        (list (List.replicate (tau * (bl.length + bn.length)) .nil ++ (h :: l))) t := by sorry
