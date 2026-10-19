-- Prove2me | Theorems.Thm_MIPRE_CL_Detyping_valid_average_le
-- name    : MIPRE.CL.Detyping.valid_average_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:13:51.900428+00:00
-- url     : https://prove2.me/theorems/875898eb-5498-4989-8f0f-b0f00e30497f
-- title:
--   Conditioning a nonnegative quantity on valid graph seeds costs at most 16 ^ |T|
-- statement:
--   A statement of the module `MIPRE.Foundations.CL.DetypingSoundness` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Same-state soundness of finite-game detyping. Restricting to the fixed graph views gives a strategy for the typed game on literally the same state. The only loss is conditioning on the valid graph event. This proves the finite-game core of `types.tex`, `lem:detyping-verifiers`; the program's answer cutoff and runtime remain separate obligations.
--
--   Conditioning a nonnegative quantity on valid graph seeds costs at most `16 ^ |T|`.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.CL
--   open MIPRE.CL.Detyping
--   open Finset Classical
--   variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]
--
--   theorem MIPRE.CL.Detyping.valid_average_le (E : T → T → Prop) [DecidableRel E] (hne : (Graph.edges E).Nonempty)
--       (f : (Graph.Coord T → ZMod 2) → (ι → ZMod 2) → ℝ) (hf : ∀ g v, 0 ≤ f g v) :
--       (∑ g ∈ Graph.validSeeds E, ∑ v, f g v) /
--           ((Graph.validSeeds E).card * Fintype.card (ι → ZMod 2)) ≤
--         (16 : ℝ) ^ Fintype.card T *
--           ((∑ g, ∑ v, f g v) / ((16 : ℝ) ^ Fintype.card T * Fintype.card (ι → ZMod 2)))
--   ```
--
--   **Formalization Note** `MIPRE.CL.Detyping.valid_average_le` is declared in `MIPRE/Foundations/CL/DetypingSoundness.lean`, lines 23–45. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/DetypingSoundness.lean#L23-L45; blueprint lem:detype-game-soundness

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Graph
import Definitions.Def_MIPRE_Foundations_CL_Detyping
import Definitions.Def_MIPRE_Foundations_CL_DetypingLaw
import Definitions.Def_MIPRE_Foundations_SampledGame
import Definitions.Def_MIPRE_Foundations_CL_DetypingGame

open MIPRE
open MIPRE.CL
open MIPRE.CL.Detyping
open Finset Classical
variable {T ι : Type*} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]

theorem MIPRE.CL.Detyping.valid_average_le (E : T → T → Prop) [DecidableRel E] (hne : (Graph.edges E).Nonempty)
    (f : (Graph.Coord T → ZMod 2) → (ι → ZMod 2) → ℝ) (hf : ∀ g v, 0 ≤ f g v) :
    (∑ g ∈ Graph.validSeeds E, ∑ v, f g v) /
        ((Graph.validSeeds E).card * Fintype.card (ι → ZMod 2)) ≤
      (16 : ℝ) ^ Fintype.card T *
        ((∑ g, ∑ v, f g v) / ((16 : ℝ) ^ Fintype.card T * Fintype.card (ι → ZMod 2))) := by sorry
