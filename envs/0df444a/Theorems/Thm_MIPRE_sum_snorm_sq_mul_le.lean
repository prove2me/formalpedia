-- Prove2me | Theorems.Thm_MIPRE_sum_snorm_sq_mul_le
-- name    : MIPRE.sum_snorm_sq_mul_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:13:56.28464+00:00
-- url     : https://prove2.me/theorems/ca480c9a-701b-443b-8125-3b8b69c91037
-- title:
--   A family of operators with sum_i F_i^dag F_i <= Id costs nothing in front
-- statement:
--   A statement of the module `MIPRE.Foundations.Commutation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The commutation analysis. Blueprint `lem:commutation-analysis` (the paper's, in `games.tex`), and the two facts it runs on. It is the step that turns *consistency with a joint measurement on the other side* into *approximate commutation on one side*, and it is the only place in the Pauli appendix where projectivity of a measurement is genuinely used.
--
--   **A family of operators with `sum_i F_i^dag F_i <= Id` costs nothing in front.**
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder
--   variable {N : Type*} [Fintype N] [DecidableEq N]
--
--   theorem MIPRE.sum_snorm_sq_mul_le {ι : Type*} [Fintype ι] (v : N → ℂ)
--       (F : ι → Matrix N N ℂ) (hF : ∑ i, (F i)ᴴ * F i ≤ (1 : Matrix N N ℂ))
--       (M : Matrix N N ℂ) :
--       ∑ i, snorm v (F i * M) ^ 2 ≤ snorm v M ^ 2
--   ```
--
--   **Formalization Note** `MIPRE.sum_snorm_sq_mul_le` is declared in `MIPRE/Foundations/Commutation.lean`, lines 86–107. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Commutation.lean#L86-L107; blueprint lem:commutation-analysis

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
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation

open MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]

theorem MIPRE.sum_snorm_sq_mul_le {ι : Type*} [Fintype ι] (v : N → ℂ)
    (F : ι → Matrix N N ℂ) (hF : ∑ i, (F i)ᴴ * F i ≤ (1 : Matrix N N ℂ))
    (M : Matrix N N ℂ) :
    ∑ i, snorm v (F i * M) ^ 2 ≤ snorm v M ^ 2 := by sorry
