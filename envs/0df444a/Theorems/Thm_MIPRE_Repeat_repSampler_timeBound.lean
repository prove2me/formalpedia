-- Prove2me | Theorems.Thm_MIPRE_Repeat_repSampler_timeBound
-- name    : MIPRE.Repeat.repSampler_timeBound
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-16T15:46:27.293981+00:00
-- url     : https://prove2.me/theorems/ae221fbc-0ff4-4059-bd32-4c08cf825908
-- title:
--   The running time of the repeated sampler: constants c, m, e uniform in everything such that, whenever W dominates the parameters at n and the input sampler runs within…
-- statement:
--   A statement of the module `MIPRE.Foundations.Repeat.SamplerCost` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The running time of the repeated sampler. `repSampler_timeBound`: when the input sampler runs within `R.S (|d| + 1)^{R.k}` at index `n` and has dimension at most `R.d` there, the repeated sampler on `(λ, τ)` runs within `c (W + 1)^m (|d| + 1)^{e (R.k + 1)}` for constants `c, m, e` independent of everything, `W` any number dominating `R.S`, `R.d`, `λ`, `τ`, `n`, the description length of the input sampler, the repetition count and `10^{R.k}` (the input's time on the dimension query). The cost is the explicit one of `repSampCore_runs_any`, each of whose pieces is a sum and product of quantities…
--
--   **The running time of the repeated sampler**: constants `c, m, e` uniform in everything
--   such that, whenever `W` dominates the parameters at `n` and the input sampler runs within
--   `R.S (|d| + 1)^{R.k}` there, the repeated sampler runs within
--   `c (W + 1)^m (|d| + 1)^{e (R.k + 1)}`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Repeat
--   open MIPRE.Cost MIPRE.Cost.Data MIPRE.Cost.Prog MIPRE.CL
--   variable {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)
--
--   theorem MIPRE.Repeat.repSampler_timeBound : ∃ c m e, ∀ {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ)
--       (R : Budget) (W : ℕ), SampDom S lam tau n R W → S.TimeBoundAt n R.S R.k →
--       (repSampler S lam tau).TimeBoundAt n (c * (W + 1) ^ m) (e * (R.k + 1))
--   ```
--
--   **Formalization Note** `MIPRE.Repeat.repSampler_timeBound` is declared in `MIPRE/Foundations/Repeat/SamplerCost.lean`, lines 269–294. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Repeat/SamplerCost.lean#L269-L294

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_Pipeline_Repetition
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
import Definitions.Def_MIPRE_Foundations_Repeat_RepSampler
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_Repeat_SamplerCost

open MIPRE
open MIPRE.Repeat
open MIPRE.Cost MIPRE.Cost.Data MIPRE.Cost.Prog MIPRE.CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ) (R : Budget) (W : ℕ)

theorem MIPRE.Repeat.repSampler_timeBound : ∃ c m e, ∀ {ℓ : ℕ} (S : CL.Sampler ℓ) (lam tau n : ℕ)
    (R : Budget) (W : ℕ), SampDom S lam tau n R W → S.TimeBoundAt n R.S R.k →
    (repSampler S lam tau).TimeBoundAt n (c * (W + 1) ^ m) (e * (R.k + 1)) := by sorry
