-- Prove2me | Theorems.Thm_MIPRE_CL_ProductSampler_prog_time
-- name    : MIPRE.CL.ProductSampler.prog_time
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:37:32.973391+00:00
-- url     : https://prove2.me/theorems/d64f1c31-3f4d-4eca-a36c-318868a8846e
-- title:
--   The running time of the product sampler's program, on every input: dominated as soon as the parameter routine runs within a dominated time, the two programs have dominated…
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.ProductSamplerCost` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The running time of the product sampler. `CL.TypedSampler.prodDirect` runs the parameter routine of its direct half through the universal machine, then routes the query: at most one call to the typed half's program, again through the universal machine, on a query at most linearly larger than the typed query (`route_call_size`), and polynomial-time work on the parameters around it. So its running time is dominated, in the sense of `MIPRE.Pipeline.PDom`, as soon as the parameter routine's is and the typed half runs within a monomial coefficient at degree `e (K + 1)` (`prog_time`), on every…
--
--   **The running time of the product sampler's program**, on every input: dominated as soon as
--   the parameter routine runs within a dominated time, the two programs have dominated sizes, and
--   `A`'s program runs within a monomial coefficient at degree `eA (K + 1)`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.CL
--   open MIPRE.CL.ProductSampler
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun MIPRE.CL.Detyping.Program MIPRE.Pipeline
--   variable (B : PolyTimeFun DirectInput BitStr) (D : PolyTimeFun Data Unary)
--
--   theorem MIPRE.CL.ProductSampler.prog_time (ℓa cp mp ep cs ms es cA mA eA : ℕ) : ∃ C M E, ∀ {W K : ℕ} (ap pp : Prog)
--       (n : ℕ) (pdn : Data) (BA : ℕ), n ≤ W →
--       (∀ {X : ℕ}, 1 ≤ X → PRuns W X K cp mp ep pp (encode n) pdn) →
--       (∀ {X : ℕ}, 1 ≤ X → PDom W X K cs ms es (esize ap + esize pp)) →
--       BA ≤ cA * (W + 1) ^ mA →
--       (∀ d, HaltsWithin ap (.cons (encode n) d) (BA * (d.size + 1) ^ (eA * (K + 1)))) →
--       ∀ q : Data, ∃ r t, PDom W (q.size + 1) K C M E t ∧
--         (prog B D ap ℓa pp).Runs (.cons (encode n) q) r t
--   ```
--
--   **Formalization Note** `MIPRE.CL.ProductSampler.prog_time` is declared in `MIPRE/Foundations/CL/ProductSamplerCost.lean`, lines 211–308. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/ProductSamplerCost.lean#L211-L308; blueprint lem:ar-typed-sampler

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
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
import Mathlib.LinearAlgebra.Basis.Defs
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
import Definitions.Def_MIPRE_Foundations_CL_Product
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_CL_ProductSampler
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
import Definitions.Def_MIPRE_Foundations_CL_ProductSamplerProg
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgQueries
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgSampler
import Definitions.Def_MIPRE_Foundations_CL_DetypingProgCost
import Definitions.Def_MIPRE_Foundations_Cost_While
import Definitions.Def_MIPRE_Foundations_Pipeline_UnaryArith
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDom
import Definitions.Def_MIPRE_Foundations_Pipeline_PowDomRun
import Definitions.Def_MIPRE_Foundations_CL_ProductSamplerCost

open MIPRE
open MIPRE.CL
open MIPRE.CL.ProductSampler
open MIPRE.Cost MIPRE.Cost.PolyTimeFun MIPRE.CL.Detyping.Program MIPRE.Pipeline
variable (B : PolyTimeFun DirectInput BitStr) (D : PolyTimeFun Data Unary)

theorem MIPRE.CL.ProductSampler.prog_time (ℓa cp mp ep cs ms es cA mA eA : ℕ) : ∃ C M E, ∀ {W K : ℕ} (ap pp : Prog)
    (n : ℕ) (pdn : Data) (BA : ℕ), n ≤ W →
    (∀ {X : ℕ}, 1 ≤ X → PRuns W X K cp mp ep pp (encode n) pdn) →
    (∀ {X : ℕ}, 1 ≤ X → PDom W X K cs ms es (esize ap + esize pp)) →
    BA ≤ cA * (W + 1) ^ mA →
    (∀ d, HaltsWithin ap (.cons (encode n) d) (BA * (d.size + 1) ^ (eA * (K + 1)))) →
    ∀ q : Data, ∃ r t, PDom W (q.size + 1) K C M E t ∧
      (prog B D ap ℓa pp).Runs (.cons (encode n) q) r t := by sorry
