-- Prove2me | Theorems.Thm_MIPRE_sum_snorm_sq_cool
-- name    : MIPRE.sum_snorm_sq_cool
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:59:26.299382+00:00
-- url     : https://prove2.me/theorems/5c9e2e96-b15f-4000-aea6-80c1554bff71
-- title:
--   lem:cool-closeness-fact, in its partition form. A projective measurement A that is delta-close to a family B stays delta-close to it after multiplying each element…
-- statement:
--   A statement of the module `MIPRE.Foundations.Commutation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The commutation analysis. Blueprint `lem:commutation-analysis` (the paper's, in `games.tex`), and the two facts it runs on. It is the step that turns *consistency with a joint measurement on the other side* into *approximate commutation on one side*, and it is the only place in the Pauli appendix where projectivity of a measurement is genuinely used.
--
--   **`lem:cool-closeness-fact`, in its partition form.** A projective measurement `A` that is
--   `delta`-close to a family `B` stays `delta`-close to it after multiplying each element by `A`'s own
--   element and summing over the fibres of an outcome map --- *simultaneously* over all the fibres,
--   which is what the consumers need: the single-subset form applied to the `q` fibres of an outcome
--   map one at a time would cost a factor `q`.
--
--   The two facts are that projectivity kills the cross terms inside a fibre, and that each `A i` is a
--   contraction. The fibres being disjoint is what lets the outer sum be absorbed.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder
--   variable {N : Type*} [Fintype N] [DecidableEq N]
--
--   theorem MIPRE.sum_snorm_sq_cool {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
--       (v : N → ℂ) {A : ι → Matrix N N ℂ} (hA : IsPVM A) (B : ι → Matrix N N ℂ) (f : ι → κ) :
--       ∑ k : κ, snorm v (∑ i ∈ univ.filter fun i => f i = k, (A i - A i * B i)) ^ 2
--         ≤ ∑ i, snorm v (A i - B i) ^ 2
--   ```
--
--   **Formalization Note** `MIPRE.sum_snorm_sq_cool` is declared in `MIPRE/Foundations/Commutation.lean`, lines 142–182. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Commutation.lean#L142-L182; blueprint lem:cool-closeness-fact

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]

theorem MIPRE.sum_snorm_sq_cool {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (v : N → ℂ) {A : ι → Matrix N N ℂ} (hA : IsPVM A) (B : ι → Matrix N N ℂ) (f : ι → κ) :
    ∑ k : κ, snorm v (∑ i ∈ univ.filter fun i => f i = k, (A i - A i * B i)) ^ 2
      ≤ ∑ i, snorm v (A i - B i) ^ 2 := by sorry
