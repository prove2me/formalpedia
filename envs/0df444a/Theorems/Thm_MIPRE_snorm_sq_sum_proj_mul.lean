-- Prove2me | Theorems.Thm_MIPRE_snorm_sq_sum_proj_mul
-- name    : MIPRE.snorm_sq_sum_proj_mul
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:59:29.422901+00:00
-- url     : https://prove2.me/theorems/e1b5e523-f6d5-4ea0-955f-0b4c83e8a720
-- title:
--   A sum of mutually orthogonal projections times arbitrary operators has orthogonal terms. The cross terms carry P i * P j = 0, so the squared state norm is additive ---…
-- statement:
--   A statement of the module `MIPRE.Foundations.Commutation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The commutation analysis. Blueprint `lem:commutation-analysis` (the paper's, in `games.tex`), and the two facts it runs on. It is the step that turns *consistency with a joint measurement on the other side* into *approximate commutation on one side*, and it is the only place in the Pauli appendix where projectivity of a measurement is genuinely used.
--
--   **A sum of mutually orthogonal projections times arbitrary operators has orthogonal terms.**
--   The cross terms carry `P i * P j = 0`, so the squared state norm is additive --- exactly, and with
--   no appeal to the size of the index set.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder
--   variable {N : Type*} [Fintype N] [DecidableEq N]
--
--   theorem MIPRE.snorm_sq_sum_proj_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (v : N → ℂ)
--       {P : ι → Matrix N N ℂ} (hPsa : ∀ i, (P i)ᴴ = P i)
--       (horth : ∀ i j, i ≠ j → P i * P j = 0) (W : ι → Matrix N N ℂ) (s : Finset ι) :
--       snorm v (∑ i ∈ s, P i * W i) ^ 2 = ∑ i ∈ s, snorm v (P i * W i) ^ 2
--   ```
--
--   **Formalization Note** `MIPRE.snorm_sq_sum_proj_mul` is declared in `MIPRE/Foundations/Commutation.lean`, lines 123–140. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Commutation.lean#L123-L140; blueprint lem:cool-closeness-fact

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

theorem MIPRE.snorm_sq_sum_proj_mul {ι : Type*} [Fintype ι] [DecidableEq ι] (v : N → ℂ)
    {P : ι → Matrix N N ℂ} (hPsa : ∀ i, (P i)ᴴ = P i)
    (horth : ∀ i j, i ≠ j → P i * P j = 0) (W : ι → Matrix N N ℂ) (s : Finset ι) :
    snorm v (∑ i ∈ s, P i * W i) ^ 2 = ∑ i ∈ s, snorm v (P i * W i) ^ 2 := by sorry
