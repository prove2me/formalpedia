-- Prove2me | Theorems.Thm_MIPRE_sum_snorm_sq_triangle3
-- name    : MIPRE.sum_snorm_sq_triangle3
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:13:48.706992+00:00
-- url     : https://prove2.me/theorems/796c01ab-109d-4adc-b88f-1de25b102c42
-- title:
--   The three-term triangle inequality for a family of deviations
-- statement:
--   A statement of the module `MIPRE.Foundations.Commutation` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The commutation analysis. Blueprint `lem:commutation-analysis` (the paper's, in `games.tex`), and the two facts it runs on. It is the step that turns *consistency with a joint measurement on the other side* into *approximate commutation on one side*, and it is the only place in the Pauli appendix where projectivity of a measurement is genuinely used.
--
--   The three-term triangle inequality for a family of deviations.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open Finset Matrix
--   open scoped ComplexOrder MatrixOrder
--   variable {N : Type*} [Fintype N] [DecidableEq N]
--
--   theorem MIPRE.sum_snorm_sq_triangle3 {κ : Type*} [Fintype κ] (v : N → ℂ)
--       (P Q R T : κ → Matrix N N ℂ) :
--       ∑ o, snorm v (P o - T o) ^ 2
--         ≤ 3 * ∑ o, snorm v (P o - Q o) ^ 2 + 3 * ∑ o, snorm v (Q o - R o) ^ 2
--           + 3 * ∑ o, snorm v (R o - T o) ^ 2
--   ```
--
--   **Formalization Note** `MIPRE.sum_snorm_sq_triangle3` is declared in `MIPRE/Foundations/Commutation.lean`, lines 197–216. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Commutation.lean#L197-L216; blueprint lem:commutation-analysis

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

theorem MIPRE.sum_snorm_sq_triangle3 {κ : Type*} [Fintype κ] (v : N → ℂ)
    (P Q R T : κ → Matrix N N ℂ) :
    ∑ o, snorm v (P o - T o) ^ 2
      ≤ 3 * ∑ o, snorm v (P o - Q o) ^ 2 + 3 * ∑ o, snorm v (Q o - R o) ^ 2
        + 3 * ∑ o, snorm v (R o - T o) ^ 2 := by sorry
