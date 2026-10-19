-- Prove2me | Theorems.Thm_MIPRE_LIDT_CL_rep_add_lineParam_smul
-- name    : MIPRE.LIDT.CL.rep_add_lineParam_smul
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:27:46.09398+00:00
-- url     : https://prove2.me/theorems/cdf7c4b9-06ca-4401-844c-349ed50325c1
-- title:
--   Every point lies on its own seeded line, at the parameter lineParam computes, whether or not the direction vanishes
-- statement:
--   A statement of the module `MIPRE.Background.LIDT.Adapter.Value` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). The value of a strategy for the seeded test, sample by sample. The seeded test's question distribution is the push-forward of the uniform distribution on `Sample F m` under the two typed question maps. A strategy's failure probability is therefore the average over samples of the conditional failure at the two questions the sample generates (`one_sub_povmValue_clGame`), and that average splits into the nine ordered type pairs (`sum_sample_eq`). The padded strategy of the Pauli basis test is analysed one type pair at a time, which is what these two identities are for. The file also records two…
--
--   **Every point lies on its own seeded line, at the parameter `lineParam` computes**, whether
--   or not the direction vanishes.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LIDT
--   open MIPRE.LIDT.CL
--   open Finset MIPRE
--   variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ}
--
--   theorem MIPRE.LIDT.CL.rep_add_lineParam_smul (w u : Point F m) :
--       rep w u + lineParam (rep w u) w u • w = u
--   ```
--
--   **Formalization Note** `MIPRE.LIDT.CL.rep_add_lineParam_smul` is declared in `MIPRE/Background/LIDT/Adapter/Value.lean`, lines 60–76. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Background/LIDT/Adapter/Value.lean#L60-L76; blueprint lem:qld-global-setup

import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Value

open MIPRE
open MIPRE.LIDT
open MIPRE.LIDT.CL
open Finset MIPRE
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ}
omit [Fintype F]

theorem MIPRE.LIDT.CL.rep_add_lineParam_smul (w u : Point F m) :
    rep w u + lineParam (rep w u) w u • w = u := by sorry
