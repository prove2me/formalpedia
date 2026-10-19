-- Prove2me | Theorems.Thm_MIPRE_Cost_Prog_decMain_inv
-- name    : MIPRE.Cost.Prog.decMain_inv
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:25:10.731915+00:00
-- url     : https://prove2.me/theorems/fca0a389-d2db-43bc-9e90-2fcd8f51e3e2
-- title:
--   Inversion of the main program
-- statement:
--   A statement of the module `MIPRE.Foundations.Repeat.DecMain` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The program of the repeated decider. The decider of `ComputeParrepVerifier` (`thm:parallel-repetition`; `planning/repetition-verifier.md`, R3(c)) as a program of the ambient model, before the s-m-n construction. On `((S̄, D̄, λ, τ, β), (n, x, y, a, b))` it 1. sanitizes `x, y, a, b` into bit strings (`bitsProg`: every element read as a bit), so that the rest of the program is total on every datum; 2. computes, in unary, `s = s(n)` from `S̄`, `m = τ(|λ| + |n|)`, the repetition count `k = 2^m`, the question length `k s`, and the parse length `B = 2^{β(|λ| + |n|)}`; 3. checks `|x| = |y| = k s`…
--
--   **Inversion of the main program.**
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Cost
--   open MIPRE.Cost.Prog
--   open MIPRE.Cost.Data
--
--   theorem MIPRE.Cost.Prog.decMain_inv {univ : Prog} (hU : univ.WellScoped 1) (inp : Data) {out : Data} {t : ℕ}
--       (h : Eval [inp] (decMain univ) out t) :
--       ∃ p t₀, Eval [inp] (prepProg univ) p t₀ ∧
--         ((p = .nil ∧ out = .nil) ∨
--           ∃ st₀ st₁, p = .cons st₀ st₁ ∧ ∃ t₁, Eval [Data.cons st₀ st₁] (.loop (coordBody univ)) out t₁)
--   ```
--
--   **Formalization Note** `MIPRE.Cost.Prog.decMain_inv` is declared in `MIPRE/Foundations/Repeat/DecMain.lean`, lines 456–477. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Repeat/DecMain.lean#L456-L477

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
import Mathlib.Logic.Function.Iterate
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
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Repeat_DecLoop
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Repeat_DecMain

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open MIPRE.Cost.Data

theorem MIPRE.Cost.Prog.decMain_inv {univ : Prog} (hU : univ.WellScoped 1) (inp : Data) {out : Data} {t : ℕ}
    (h : Eval [inp] (decMain univ) out t) :
    ∃ p t₀, Eval [inp] (prepProg univ) p t₀ ∧
      ((p = .nil ∧ out = .nil) ∨
        ∃ st₀ st₁, p = .cons st₀ st₁ ∧ ∃ t₁, Eval [Data.cons st₀ st₁] (.loop (coordBody univ)) out t₁) := by sorry
