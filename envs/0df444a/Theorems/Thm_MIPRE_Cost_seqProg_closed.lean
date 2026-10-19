-- Prove2me | Theorems.Thm_MIPRE_Cost_seqProg_closed
-- name    : MIPRE.Cost.seqProg_closed
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:21:20.73041+00:00
-- url     : https://prove2.me/theorems/f0bdd4fe-34a0-49f0-9df6-afc124eb9b09
-- title:
--   Lemma seqProg_closed of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.Cost.While` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Iterating a polynomial-time step, and running programs in sequence. Two program combinators for routines whose running time is not polynomial in the size of their input, such as the computation of `(λn + 1)^μ` from binary `λ, n, μ`: * `whileProg f` iterates a total step `f : Data → Bool × Data` from a state, continuing on `(true, s')` with the state `s'` and stopping on `(false, r)` with the result `r`; a run of `N + 1` steps costs the sum of the steps' bounds (`whileProg_runs`); * `seqProg p q` runs `q` on the output of `p` (`seqProg_runs`).
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.Cost
--   open MIPRE.Cost.PolyTimeFun
--
--   theorem MIPRE.Cost.seqProg_closed {p q : Prog} (hp : p.WellScoped 1) (hq : q.WellScoped 1) :
--       (seqProg p q).WellScoped 1
--   ```
--
--   **Formalization Note** `MIPRE.Cost.seqProg_closed` is declared in `MIPRE/Foundations/Cost/While.lean`, lines 54–56. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/While.lean#L54-L56

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

theorem MIPRE.Cost.seqProg_closed {p q : Prog} (hp : p.WellScoped 1) (hq : q.WellScoped 1) :
    (seqProg p q).WellScoped 1 := by sorry
