-- Prove2me | Theorems.Thm_MIPRE_CL_CLFun_ExactlyOn_outputPrefix_self
-- name    : MIPRE.CL.CLFun.ExactlyOn.outputPrefix_self
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:10:23.676152+00:00
-- url     : https://prove2.me/theorems/bcd95aca-f6f7-4c21-b7cf-215a1ac63878
-- title:
--   No image-membership condition is used to compute prefixes of claimed answers
-- statement:
--   A statement of the module `MIPRE.Foundations.Introspection.SamplingPrefix` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Reading prefixes from arbitrary claimed CL outputs. The sampling test coarse-grains the entire answer alphabet, not merely the image of the CL map. The prefix map therefore follows the claimed output's coordinate branches and does not apply the stage linear maps again.
--
--   No image-membership condition is used to compute prefixes of claimed answers.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.CL
--   open MIPRE.CL.CLFun
--   open Finset
--   variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}
--
--   theorem MIPRE.CL.CLFun.ExactlyOn.outputPrefix_self {P : CLFun F ι ℓ} {T : Finset ι}
--       (hP : P.ExactlyOn T) (y : ι → F) : P.outputPrefix ℓ (proj T y) = proj T y
--   ```
--
--   **Formalization Note** `MIPRE.CL.CLFun.ExactlyOn.outputPrefix_self` is declared in `MIPRE/Foundations/Introspection/SamplingPrefix.lean`, lines 57–71. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Introspection/SamplingPrefix.lean#L57-L71; blueprint lem:intro-subtest-estimates

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Introspection_SamplingPrefix

open MIPRE
open MIPRE.CL
open MIPRE.CL.CLFun
open Finset
variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] {ℓ : ℕ}

theorem MIPRE.CL.CLFun.ExactlyOn.outputPrefix_self {P : CLFun F ι ℓ} {T : Finset ι}
    (hP : P.ExactlyOn T) (y : ι → F) : P.outputPrefix ℓ (proj T y) = proj T y := by sorry
