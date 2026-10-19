-- Prove2me | Theorems.Thm_MIPRE_Pipeline_PRuns_stage
-- name    : MIPRE.Pipeline.PRuns.stage
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:37:57.442981+00:00
-- url     : https://prove2.me/theorems/0b599df3-a19e-45d5-a9db-21675fe726fb
-- title:
--   A stage keeping a context: stageProg pre p post on x, with pre x = (a, ctx)
-- statement:
--   A statement of the module `MIPRE.Foundations.Pipeline.PowDomRun` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Runs within a powered monomial. `PRuns W X K c m e p x r`: the program `p` runs from `x` to `r` at a cost below `(c (W + 1)^m X^e)^{K + 1}` (`MIPRE.Pipeline.PDom`). The combinators follow the program constructors the pipeline's routines are built from — a polynomial-time function's code (`ptf`), sequencing (`seq`), a stage keeping a context (`stage`), hardcoding (`hardcode`), the universal machine (`univ`), and the two unary loops (`toUnary`, `pow`) — and each returns its constants from those of its arguments, so that a chain of them has constants uniform in `W`, `X`, `K` and the data. The…
--
--   **A stage** keeping a context: `stageProg pre p post` on `x`, with `pre x = (a, ctx)`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Pipeline
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun MIPRE.CL.Detyping.Program MIPRE.LowDegree.DegreeArithmetic
--   variable {W X K : ℕ}
--
--   theorem MIPRE.Pipeline.PRuns.stage (pre : PolyTimeFun Data Data) (post : PolyTimeFun (Data × Data) Data)
--       (c m e c' m' e' : ℕ) : ∃ C M E, ∀ {W X K : ℕ} {p : Prog}, p.WellScoped 1 →
--         ∀ (x a ctx r : Data), 1 ≤ X → pre x = .cons a ctx → PDom W X K c m e x.size →
--         PRuns W X K c' m' e' p a r → PRuns W X K C M E (stageProg pre p post) x (post (ctx, r))
--   ```
--
--   **Formalization Note** `MIPRE.Pipeline.PRuns.stage` is declared in `MIPRE/Foundations/Pipeline/PowDomRun.lean`, lines 179–204. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Pipeline/PowDomRun.lean#L179-L204

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryArithmetic
import Definitions.Def_MIPRE_Foundations_Cost_BinaryCompare
import Definitions.Def_MIPRE_Foundations_Cost_TreeBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgFinite
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgParse
import Definitions.Def_MIPRE_Foundations_CL_DetypingQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgBits
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCall
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgRoute
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_Cost_While
import Definitions.Def_MIPRE_Foundations_Pipeline_UnaryArith
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDom
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDomRun

open MIPRE
open MIPRE.Pipeline
open MIPRE.Cost MIPRE.Cost.PolyTimeFun MIPRE.CL.Detyping.Program MIPRE.LowDegree.DegreeArithmetic
variable {W X K : ℕ}

theorem MIPRE.Pipeline.PRuns.stage (pre : PolyTimeFun Data Data) (post : PolyTimeFun (Data × Data) Data)
    (c m e c' m' e' : ℕ) : ∃ C M E, ∀ {W X K : ℕ} {p : Prog}, p.WellScoped 1 →
      ∀ (x a ctx r : Data), 1 ≤ X → pre x = .cons a ctx → PDom W X K c m e x.size →
      PRuns W X K c' m' e' p a r → PRuns W X K C M E (stageProg pre p post) x (post (ctx, r)) := by sorry
