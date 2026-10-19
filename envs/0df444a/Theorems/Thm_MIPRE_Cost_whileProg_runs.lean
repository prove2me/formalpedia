-- Prove2me | Theorems.Thm_MIPRE_Cost_whileProg_runs
-- name    : MIPRE.Cost.whileProg_runs
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:21:19.64752+00:00
-- url     : https://prove2.me/theorems/4b701a40-4f91-48e9-a03c-84f5c7b9f93a
-- title:
--   A run of the loop through the states s 0, …, s N, stopping at s N with r
-- statement:
--   A statement of the module `MIPRE.Foundations.Cost.While` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Iterating a polynomial-time step, and running programs in sequence. Two program combinators for routines whose running time is not polynomial in the size of their input, such as the computation of `(λn + 1)^μ` from binary `λ, n, μ`: * `whileProg f` iterates a total step `f : Data → Bool × Data` from a state, continuing on `(true, s')` with the state `s'` and stopping on `(false, r)` with the result `r`; a run of `N + 1` steps costs the sum of the steps' bounds (`whileProg_runs`); * `seqProg p q` runs `q` on the output of `p` (`seqProg_runs`).
--
--   **A run of the loop** through the states `s 0, …, s N`, stopping at `s N` with `r`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Cost
--   open MIPRE.Cost.PolyTimeFun
--
--   theorem MIPRE.Cost.whileProg_runs (f : PolyTimeFun Data (Bool × Data)) (N : ℕ) (s : ℕ → Data) (r : Data)
--       (hcont : ∀ i < N, f (s i) = (true, s (i + 1))) (hstop : f (s N) = (false, r)) :
--       ∃ t ≤ ∑ i ∈ Finset.range (N + 1), (f.timeBound.eval (s i).size + 1),
--         (whileProg f).Runs (s 0) r t
--   ```
--
--   **Formalization Note** `MIPRE.Cost.whileProg_runs` is declared in `MIPRE/Foundations/Cost/While.lean`, lines 30–49. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/While.lean#L30-L49

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_Cost_While

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.PolyTimeFun

theorem MIPRE.Cost.whileProg_runs (f : PolyTimeFun Data (Bool × Data)) (N : ℕ) (s : ℕ → Data) (r : Data)
    (hcont : ∀ i < N, f (s i) = (true, s (i + 1))) (hstop : f (s N) = (false, r)) :
    ∃ t ≤ ∑ i ∈ Finset.range (N + 1), (f.timeBound.eval (s i).size + 1),
      (whileProg f).Runs (s 0) r t := by sorry
